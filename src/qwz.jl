include("../quantum-wz/QuantumWZ.jl")

# Notation. The paper writes q, U, R, Υ; QuantumWZ writes t, X, Y, T:
#   quantum plane 𝔸 = ℚ(q)⟨U,R⟩/(RU − qUR)  is  qwzctx.A  with  U = X, R = Y;
#   operator algebra 𝒪 = ℚ(q)⟨R,Υ⟩/(ΥR − qRΥ)  is  qwzctx.O  with  R = Yo, Υ = T.

const qwzctx = QuantumWZ.setup() # move to __init__()

"""
    Problem

A normalized marginal system `(L, f, d)` over the operator algebra 𝒪 (paper, eq. (9)):
the series `m = (m_i)` is the unique solution of `L m = f`, and `C = Σ_i d[i] m_i` is the
marginal ρ(S) of the series S that the system realizes. `L ≡ I mod q`.
"""
const Problem = @NamedTuple begin
    L::Matrix
    f::Vector
    d::Vector
end

"""
    attempt(p::Problem; N = 24, kw...)

Search a certificate that ε(S) = 0 for the series S realized by `p`, by the finite searches of
§3.8 and Appendix A of the paper (`QuantumWZ.attempt`, which documents `kw`). The result has a
field `status`:

* `:nonzero`: some ν(b_n) < n + 1, so ε(S) ≠ 0 (Theorem A(3), Lemma 3.5);
* `:proved`: ε(S) = 0, by the method in the field `method`: `:zero_marginal` (C = 0, decided
  from finitely many coefficients, Lemma 3.4), `:rational` or `:polynomial` (operator
  witnesses, Appendix A), `:channels` (partial sums b_n along progressions are sums of
  first-order series that decay or cancel by dilation witnesses, Proposition 3.7);
* `:unknown`: nothing found within the bounds; this is not a disproof.
"""
attempt(p::Problem; N = 24, kw...) = QuantumWZ.attempt(qwzctx, p.L, p.f, p.d; N = N, kw...)

"""
    compile(t::Automaton)
    compile(s::AbstractString)

The normalized marginal system (paper, eqs. (8)–(9)) of the path series of an automaton:
an `Automaton`, or a string in the notation of `QuantumWZ.automaton` (\"0R1 1U1 1U∞ …\"), which
also allows weighted and nondeterministic automata (parallel arcs add their weights).
An arc i → j contributes `-q R` (letter R) or `-q Υ` (letter U) to `L[j,i]`; `f` marks the
states entered by the initial R, and `d[i] = q R` at the states left by a final U.
"""
function compile(t::Automaton{N})::Problem where N
    z = QuantumWZ.operator(qwzctx,[])
    o = z+1
    Y = qwzctx.Yo*qwzctx.t
    T = qwzctx.T*qwzctx.t
    L = [i == j ? o : z for i=1:N, j=1:N]
    f = [i == 1 ? o : z for i=1:N]
    d = [iszero(t.x[i,3]) ? z : Y for i=1:N]

    for i=1:N, s=1:2
        if !iszero(t.x[i,s])
            L[t.x[i,s],i] -= (s == 1 ? Y : T)
        end
    end

    (L = L, f, d)
end

compile(s::AbstractString)::Problem = Problem(QuantumWZ.compile(qwzctx, QuantumWZ.automaton(qwzctx, s)...))

"""
    difference(p₁, p₂)

The block-diagonal system of S₁ − S₂ (paper, §3.5): output row `[d₁; -d₂]`.
"""
function difference(p₁,p₂)::Problem
    o = QuantumWZ.operator(qwzctx,[])
    N₁ = length(p₁.f)
    N₂ = length(p₂.f)

    L = [o for i=1:N₁+N₂, j=1:N₁+N₂]
    L[1:N₁,1:N₁] = p₁.L
    L[N₁+1:N₁+N₂,N₁+1:N₁+N₂] = p₂.L

    (L = L, f = [p₁.f;p₂.f], d = [p₁.d;-p₂.d])
end

compile(t::Automaton{M},u::Automaton{N}) where {M,N} = difference(compile(t),compile(u))

"""
    bvalues(p::Problem, n)

The coefficients `b_0, …, b_n ∈ ℚ(q)` of the canonical formal boundary `b = C/(1 − R)`
(paper, eq. (11)): the partial sums of the coefficients of the marginal `C`. For a difference
of path series, `b_n` is the difference of the weighted counts of the partitions with largest
part at most `n`, and the identity holds if and only if `ν(b_n) ≥ n + 1` for all `n`
(Theorem A(3)).
"""
function bvalues(p::Problem, n::Integer)
    O = qwzctx.O
    m = QuantumWZ.solve_series(qwzctx, map(O, p.L), map(O, p.f), n)
    accumulate(+, QuantumWZ.marginal_coeffs(qwzctx, map(O, p.d), m))
end

"""
    rate_ok(p::Problem, n)

Whether `ν(b_k) ≥ k + 1` for `k ≤ n` (Theorem A(3c) up to `n`). A failure disproves the
identity (Lemma 3.5); success up to a finite `n` proves nothing.
"""
rate_ok(p::Problem, n::Integer) = all(QuantumWZ.valuation_t(b) ≥ k for (k, b) in enumerate(bvalues(p, n)))

# system is described in the form r*Q⁻¹*e with r,Q,e defined over X,Y.
# QuantumWZ.compile turns it into operator form (L,f,d) with
# L = Φ(Q'), f = ρ(r), d = Φ(e), for the maps Φ(X^a Y^b) = Y^b T^a, ρ(X^a Y^b) = Y^b

# euler_odd is: R(1-U-RR)⁻¹U, rewritten U(1-tU-t²RR)⁻¹tR = X(1-tX-t²Y²)tY
# compiled to L=[1-tT-t²Y²], f=[1], d=[tY]
"Euler's odd parts from the regular expression R(1 − U − R²)⁻¹U (paper, §1): L = [1 − qΥ − q²R²]."
function euler_odd()
    (; t, A, X, Y) = qwzctx
    QuantumWZ.compile(qwzctx, [one(A) - A(t) * X - A(t^2) * Y^2], [X], [A(t) * Y]) |> Problem
end

"Euler's distinct parts from the regular expression R(1 − R − UR)⁻¹U (paper, §1): L = [1 − qR − q²RΥ]."
function euler_distinct()
    (; t, A, X, Y) = qwzctx
    QuantumWZ.compile(qwzctx, [one(A) - A(t) * Y - A(t^2) * X * Y], [X], [A(t) * Y]) |> Problem
end
