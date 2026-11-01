# Shared setup for the scripts that reproduce the computations of
#     L. Bartholdi, "Automatic partition identities".
# Run one script with  julia --project=. paper/primc.jl,  or all with  julia --project=. paper/runall.jl.
# Equation numbers refer to the paper.

using Partitions, Oscar, Test
using Partitions: QuantumWZ, qwzctx, Problem, compile, difference, attempt, bvalues, rate_ok,
                  pathseries, npaths, spec

const ctx = qwzctx
const K = ctx.K               # ℚ(q)
const q = ctx.t               # q (QuantumWZ writes t)
const R = ctx.Yo              # R in 𝒪 = ℚ(q)⟨R,Υ⟩/(ΥR − qRΥ) (QuantumWZ writes Y)
const Υ = ctx.T               # Υ: g(R) ↦ g(qR), the image Φ(U) (QuantumWZ writes T)
const O0 = zero(ctx.O)
const O1 = one(ctx.O)

"The operator Σ c R^b Υ^a ∈ 𝒪, from triples (c, b, a)."
oper(terms...) = QuantumWZ.operator(ctx, collect(terms))

"Image under h ∈ 𝒪 of the polynomial p(R), itself given as an operator free of Υ."
act(h, p) = QuantumWZ.operator(ctx, [(c, b, 0) for (c, b, _) in QuantumWZ.pbw_terms(h * p)])

"[R^k](h·v) for an operator h and a series v given by v[k+1] = [R^k]v."
coeff_R(h, v, k) = QuantumWZ.ycoeff(ctx, h, v, k)

"The solution m of L m = f to order R^n, for a system p = (L, f, d): m[i][k+1] = [R^k]m_i."
solvesystem(p, n) = QuantumWZ.solve_series(ctx, map(ctx.O, p.L), map(ctx.O, p.f), n)

"q-adic valuation on ℚ(q)."
ν(x) = QuantumWZ.valuation_t(x)

"x ∈ ℤ[q]."
function inZq(x)
    iszero(x) && return true
    n, d = numerator(x), denominator(x)
    degree(d) == 0 && all(isone(denominator(coeff(n, i) // coeff(d, 0))) for i in 0:degree(n))
end

# Truncated power series: vectors s with s[k+1] = [x^k]s, all of the same length.
"Product of two truncated series of the same length."
smul(a, b) = [sum(a[i+1] * b[k-i+1] for i in 0:k) for k in 0:length(a)-1]

"x^k a, truncated to the length of a."
sshift(a, k) = k ≥ length(a) ? zero(a) : [zero(a[1:k]); a[1:end-k]]

"Π 1/(1 − x^e) over the exponents e (with repetitions), to order x^N."
function invprod(exps, N)
    s = [1; zeros(Int, N)]
    for e in exps, n in e:N
        s[n+1] += s[n-e+1]
    end
    s
end

"The exponents h ≤ N, each repeated mult[h mod M] times (residue conditions modulo M)."
residueexps(mult, M, N) = [h for h in 1:N for _ in 1:get(mult, mod(h, M), 0)]

"The subsets of {1, …, n}, as increasing vectors."
allsubsets(n) = (findall(isodd, [m >> k for k in 0:n-1]) for m in 0:2^n-1)

# Partitions as vectors of parts in decreasing order.
"α(λ) = λ₁ − λ₂ + λ₃ − ⋯, the alternating sum of §4.4."
altsum(λ) = sum((isodd(i) ? λ[i] : -λ[i] for i in eachindex(λ)); init = 0)

"The partitions into distinct parts of size at most N, in decreasing order."
function distinct_partitions(N)
    out = Vector{Int}[]
    function grow(λ, s, next)          # λ increasing, s = sum(λ), next = the least admissible new part
        push!(out, reverse(λ))
        for p in next:N-s
            grow([λ; p], s + p, p + 1)
        end
    end
    grow(Int[], 0, 1)
    out
end

"The partitions into distinct parts at most n, in decreasing order."
distinct_bounded(n) = (reverse(S) for S in allsubsets(n))

const PAPER_COMMON = true
