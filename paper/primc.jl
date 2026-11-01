# §4.2: Primc's identities at level two (Theorem B).
@isdefined(PAPER_DATA) || include("data.jl")

"""
F(1) = (F00, F01, F02, F11)(1) for the four-state transfer F(z) = M(z) F(q²z), F(0) = (1,1,1,1)
(eq. (18)), as power series in q to order q^N. With M(z) = M0 + z M1 + z² M2, the coefficient of
z^n is F_n = (I − q^(2n) M0)⁻¹ (q^(2n−2) M1 F_(n−1) + q^(2n−4) M2 F_(n−2)), and
(I − q^(2n) M0)⁻¹ = I + q^(2n)/(1 − q^(2n)) M0 because M0 is idempotent, M0 x = (x₁, x₁, x₁, x₁).
"""
function transfer_at_one(N)
    # entries of M1 and M2: (i, j) => (c, e) for the monomial c q^e (s = qz, t = q²z in (18))
    M1 = Dict((1,1) => (1,1), (1,2) => (2,2), (2,1) => (1,1), (2,2) => (2,2), (3,2) => (1,2), (4,2) => (2,2))
    M2 = Dict((1,1) => (1,2), (1,2) => (2,3), (1,3) => (2,4), (1,4) => (1,4), (2,2) => (1,3),
              (2,3) => (1,4), (2,4) => (1,4), (3,3) => (1,4), (4,4) => (1,4))
    Fs = [[[1; zeros(Int, N)] for _ in 1:4]]          # Fs[n+1][i] = component i of F_n
    for n in 1:N
        rhs = [zeros(Int, N + 1) for _ in 1:4]
        for (k, Mk) in ((1, M1), (2, M2)), ((i, j), (c, e)) in Mk
            n ≥ k && (rhs[i] += c * sshift(Fs[n-k+1][j], e + 2(n - k)))
        end
        corr = smul([k > 0 && k % (2n) == 0 ? 1 : 0 for k in 0:N], rhs[1])
        push!(Fs, [x + corr for x in rhs])
    end
    [sum(F[i] for F in Fs) for i in 1:4]
end

"Σ_n r^(n² + sh·n) (−r; r²)_n/(r²; r²)_n to order r^N: g(r; r²) for sh = 0, h(r; r²) for sh = 2, eq. (24)."
function gg_series(sh, N)
    total = zeros(Int, N + 1)
    for n in 0:N
        n^2 + sh * n > N && break
        t = [k == n^2 + sh * n ? 1 : 0 for k in 0:N]
        for j in 0:n-1
            t = smul(t, [k == 0 || k == 2j + 1 ? 1 : 0 for k in 0:N])    # 1 + r^(2j+1)
            t = smul(t, [k % (2j + 2) == 0 ? 1 : 0 for k in 0:N])        # 1/(1 − r^(2j+2))
        end
        total += t
    end
    total
end

@testset "§4.2: Primc's identities (Theorem B)" begin
    N = 40
    # residues with one colour, residues with two colours (modulo 8)
    prodseries(c1, c2) = invprod(residueexps(Dict([[r => 1 for r in c1]; [r => 2 for r in c2]]), 8, N), N)

    # The automata of Figure 1: 29 and 9 interior states, both with series Π_(2,0,0).
    Π200 = prodseries([2, 3, 5, 6], [4])
    adm, res = pathseries(primc_admissible, N), pathseries(primc_residues, N)
    @test [1; adm[2:end]] == Π200 && [1; res[2:end]] == Π200

    # §4.2.1: the transfer system (18) at z = 1 gives the four products of Theorem B, and its
    # component F02 is the series of the admissible automaton.
    F00, F01, F02, F11 = transfer_at_one(N)
    @test F02 == Π200                                  # (k0,k1,k2) = (2,0,0)
    @test F01 == prodseries([1, 2, 6, 7], [4])         # (1,1,0)
    @test F11 == prodseries([3, 5], [2, 6])            # (1,0,1)
    @test F00 == prodseries([1, 7], [2, 6])            # (0,2,0)

    # §4.2.2: the quadratic invariant, eq. (19) and the 60 × 20 search with one-dimensional kernel.
    Rz, z = polynomial_ring(K, :z)
    s, t = q * z, q^2 * z
    M = matrix(Rz, map(Rz, [1+s+s^2 2t*(1+s) 2t^2 t^2; 1+s t*(2+s) t^2 t^2; 1 t t^2 0; 1 2t 0 t^2]))
    Jm(w) = matrix(Rz, map(Rz, [0 0 0 1; 0 -2 0 0; 0 0 2q*w 0; 1 0 0 0]))
    λ = -q^5 * z^3 * (1 - q*z)
    @test transpose(M) * Jm(z) * M == λ * Jm(q^2 * z)
    pairs = [(a, b) for a in 1:4 for b in a:4]
    basis = [(a, b, e) for (a, b) in pairs for e in 0:1]       # J = Σ c_(a,b,e) z^e (E_ab + E_ba)
    cols = map(basis) do (a, b, e)
        B = zero_matrix(Rz, 4, 4)
        B[a, b] = z^e
        B[b, a] = z^e
        E = transpose(M) * B * M - λ * q^(2e) * B          # B(q²z) = q^(2e) B(z)
        [coeff(E[i, j], d) for (i, j) in pairs for d in 0:5]
    end
    A = reduce(hcat, cols)
    ker = QuantumWZ.kernel_field(K, A)
    @test size(A) == (60, 20) && length(ker) == 1
    c = ker[1][findfirst(!iszero, ker[1])]
    @test [x * inv(c) for x in ker[1]] == [coeff(Jm(z)[a, b], e) for (a, b, e) in basis]

    # §4.2.2: the factorization (20), H(v) = Γ₊(v) H(qv) Γ₋(v)ᵀ, where F(v²/q) = M(v²/q) F(qv²) by (18);
    # the f's stand for the four series F(qv²) = F((qv)²/q).
    S, (Q, V, f00, f01, f02, f11) = polynomial_ring(QQ, [:q, :v, :f00, :f01, :f02, :f11])
    sv, tv = V^2, Q * V^2
    Mv = matrix(S, map(S, [1+sv+sv^2 2tv*(1+sv) 2tv^2 tv^2; 1+sv tv*(2+sv) tv^2 tv^2; 1 tv tv^2 0; 1 2tv 0 tv^2]))
    Fq = [f00, f01, f02, f11]
    Fv = Mv * matrix(S, 4, 1, Fq)
    H(F, w) = matrix(S, 2, 2, [F[1], F[2] + w*F[3], F[2] - w*F[3], F[4]])
    Γ(w) = matrix(S, 2, 2, map(S, [1 + w + w^2, Q*w^2, 1, Q*w^2]))
    @test H([Fv[i, 1] for i in 1:4], V) == Γ(V) * H(Fq, Q*V) * transpose(Γ(-V))

    # §4.2.3: the telescoping certificates (25)–(26), and the searches that find them: Ψ of degree
    # ≤ 1, resp. ≤ 2 in ζ, with residual scaled by an unknown s; coefficient matrices 4 × 3 and 5 × 4.
    Sqv, (q0, v0) = polynomial_ring(QQ, [:q, :v])
    Fqv = fraction_field(Sqv)
    Qf, Vf = Fqv(q0), Fqv(v0)
    Rζ, ζ = polynomial_ring(Fqv, :ζ)
    ϖ0 = 1 - ζ - Vf*ζ*(1 + Vf*ζ)
    ϖ1 = (Vf*ζ*(1 - ζ) - Qf*Vf^2*ζ^2*(1 + Vf*ζ)) * inv(1 + Vf)
    # (1 − qζ)(r(ζ)Ψ(qζ) − Ψ(ζ) − sϖ(ζ)) with r(ζ) = vζ(1 + vζ)/(1 − qζ), linear in (Ψ, s)
    function tele_search(ϖ, deg)
        local cs = [[Vf*ζ*(1 + Vf*ζ)*(Qf*ζ)^i - (1 - Qf*ζ)*ζ^i for i in 0:deg]; [-(1 - Qf*ζ)*ϖ]]
        local As = [coeff(cc, d) for d in 0:deg+2, cc in cs]
        As, QuantumWZ.kernel_field(Fqv, As)
    end
    A0, k0 = tele_search(ϖ0, 1)
    A1, k1 = tele_search(ϖ1, 2)
    @test size(A0) == (4, 3) && length(k0) == 1 && [x * inv(k0[1][end]) for x in k0[1]] == map(Fqv, [-1, 1, 1])
    @test size(A1) == (5, 4) && length(k1) == 1 &&
          [x * inv(k1[1][end]) for x in k1[1]] == [zero(Fqv), -Vf * inv(1 + Vf), Vf * inv(1 + Vf), one(Fqv)]
    S3, (q3, v3, z3) = polynomial_ring(QQ, [:q, :v, :ζ])
    F3 = fraction_field(S3)
    Q3, V3, Z3 = F3(q3), F3(v3), F3(z3)
    r(x) = V3*x*(1 + V3*x) * inv(1 - Q3*x)
    Ψ0(x) = x - 1
    Ψ1(x) = -V3*x*(1 - x) * inv(1 + V3)
    @test r(Z3) * Ψ0(Q3*Z3) - Ψ0(Z3) == 1 - Z3 - V3*Z3*(1 + V3*Z3)                                   # (25)
    @test r(Z3) * Ψ1(Q3*Z3) - Ψ1(Z3) == (V3*Z3*(1 - Z3) - Q3*V3^2*Z3^2*(1 + V3*Z3)) * inv(1 + V3)  # (26)

    # (24) solves (21): u(v) = Γ₊(v) u(qv), coefficientwise to v^nv.
    nv = 10
    Rv, v = polynomial_ring(K, :v)
    term(n, sh) = q^(div(n*(n - 1), 2) + sh*n) * inv(prod((1 - q^j for j in 1:n); init = one(K))) *
                  v^n * prod((1 + v*q^j for j in 0:n-1); init = one(Rv))
    g, h = sum(term(n, 0) for n in 0:nv), sum(term(n, 1) for n in 0:nv)
    gq, hq = evaluate(g, q*v), evaluate(h, q*v)
    @test all(iszero(coeff(g - (1 + v + v^2)*gq - q*v^2*hq, k)) && iszero(coeff(h - gq - q*v^2*hq, k)) for k in 0:nv)

    # §4.2.4–4.2.5 at q = r², v = r, z = 1: the Göllnitz–Gordon identities (27)–(28), and (22)–(23).
    G, Hh = gg_series(0, N), gg_series(2, N)
    @test G == invprod(residueexps(Dict(1 => 1, 4 => 1, 7 => 1), 8, N), N)
    @test Hh == invprod(residueexps(Dict(3 => 1, 4 => 1, 5 => 1), 8, N), N)
    neg(a) = [isodd(k) ? -a[k+1] : a[k+1] for k in 0:N]        # a(−r)
    spread(a) = [iseven(k) ? a[k÷2+1] : 0 for k in 0:N]         # a(q) at q = r²
    @test spread(F00) == smul(G, neg(G)) && spread(F11) == smul(Hh, neg(Hh))
    @test 2 * spread(F01) == smul(G, neg(Hh)) + smul(Hh, neg(G))
    @test (2 * spread(F02))[1:N] == (smul(G, neg(Hh)) - smul(Hh, neg(G)))[2:N+1]

    # §4.2.6: certificates for the automata. The difference system has s = 29 + 9 = 38 states, and
    # ν(b_n) ≥ n + 1 (Corollary 3.6, since Theorem B holds).
    pa, pr = compile(primc_admissible), compile(primc_residues)
    @test (length(pa.f), length(pr.f)) == (29, 9)
    @test rate_ok(difference(pa, pr), 6)
end
