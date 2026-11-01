# §4.3: the Rogers–Ramanujan identities.
@isdefined(PAPER_DATA) || include("data.jl")

@testset "§4.3: Rogers–Ramanujan" begin
    N = 60
    qR, qΥ = oper((q,1,0)), oper((q,0,1))
    for (i, Σ) in ((1, (1, 4)), (2, (2, 3)))
        # The automata of Figure 2, and the sum side Σ_n q^(n² + (i−1)n)/(q)_n and the product side (31).
        sums = sum(sshift(invprod(1:n, N), n^2 + (i - 1)*n) for n in 0:isqrt(N))
        prods = invprod(residueexps(Dict(r => 1 for r in Σ), 5, N), N)
        @test [1; pathseries(rr_gap(i), N)[2:end]] == sums == prods
        @test [1; pathseries(rr_residue(i), N)[2:end]] == prods

        # The data of §4.3: L_i = diag(L_gap, L_Σ), f_i = (e_(2i−1); e_1), d_i = qR(e_1ᵀ, −χ_Σᵀ).
        pg, ps = compile(rr_gap(i)), compile(rr_residue(i))
        @test pg.L == [O1-qR O0 -qR; -qΥ O1 O0; O0 -qR O1]
        @test pg.f == [k == 2i - 1 ? O1 : O0 for k in 1:3] && pg.d == [qR, O0, O0]
        @test ps.L == [(j == k ? O1 - (mod(j, 5) in Σ ? qΥ : O0) : O0) - (k == mod1(j - 1, 5) ? qR : O0)
                       for j in 1:5, k in 1:5]                                # I₅ − qR E − qΥ I_Σ
        @test ps.f == [k == 1 ? O1 : O0 for k in 1:5] && ps.d == [mod(k, 5) in Σ ? qR : O0 for k in 1:5]
        @test rate_ok(difference(pg, ps), 10)
    end

    # The finite identities, exactly in ℚ(q, κ).
    Sqk, (q0, k0) = polynomial_ring(QQ, [:q, :κ])
    F = fraction_field(Sqk)
    Q, κ = F(q0), F(k0)
    poch(a, n) = prod((1 - a * Q^j for j in 0:n-1); init = one(F))      # (a; q)_n
    qf(n) = poch(Q, n)                                                  # (q)_n
    α1(r) = r == 0 ? one(F) : (-1)^r * Q^div(r*(r - 1), 2) * (1 + Q^r)                 # (33), γ = 1
    αq(r) = (-1)^r * Q^div(r*(r - 1), 2) * (1 - Q^(2r + 1)) * inv(1 - Q)              # (34), γ = q
    for (γ, α) in ((one(F), α1), (Q, αq)), m in 0:6                                    # unit pairs in (32)
        @test sum(α(r) * inv(qf(m - r) * poch(γ * Q, m + r)) for r in 0:m) == (m == 0 ? one(F) : zero(F))
    end
    for m in 0:6                                                                        # (36)
        @test sum(κ^k * Q^(k^2) * inv(qf(m - k) * qf(k) * poch(κ * Q, k)) for k in 0:m) ==
              inv(qf(m) * poch(κ * Q, m))
    end
    for (δ, α) in ((0, α1), (1, αq)), M in 0:6                                          # (37), γ = q^δ
        γ = Q^δ
        @test sum(γ^n * Q^(n^2) * inv(qf(n)) * qf(M) * inv(qf(M - n)) for n in 0:M) ==
              sum(γ^(2r) * Q^(2r^2) * α(r) * qf(M) * inv(qf(M - r) * poch(γ * Q, M + r)) for r in 0:M)
    end

    # The rational identity (35), and the search that finds Ψ: denominator ξ, numerator of degree ≤ 2
    # in ξ over ℚ(q, κ, ζ), residual scaled by an unknown s; the coefficient matrix is 5 × 4.
    S4, (q4, k4, z4, x4) = polynomial_ring(QQ, [:q, :κ, :ζ, :ξ])
    F4 = fraction_field(S4)
    Q4, κ4, ζ4, ξ4 = F4(q4), F4(k4), F4(z4), F4(x4)
    ratio(z, x) = κ4 * Q4 * x^2 * (1 - z * inv(x)) * inv((1 - Q4*x) * (1 - κ4*Q4*x))
    Ψ(z, x) = -z * (1 - x) * (1 - κ4*x) * inv(x)
    @test ratio(ζ4, ξ4) * Ψ(ζ4, Q4*ξ4) - Ψ(ζ4, ξ4) == (1 - ζ4) * (1 - κ4*ζ4) - (1 - ζ4 * inv(ξ4))
    Sz, (q5, k5, z5) = polynomial_ring(QQ, [:q, :κ, :ζ])
    F5 = fraction_field(Sz)
    Q5, κ5, ζ5 = F5(q5), F5(k5), F5(z5)
    Rξ, ξ = polynomial_ring(F5, :ξ)
    # ξ(1 − qξ)(1 − κqξ)(r Ψ(ζ, qξ) − Ψ(ζ, ξ) − s ϖ) for Ψ = Σ_(b ≤ 2) c_b ξ^(b−1), linear in (c, s)
    cs = [[κ5*ξ*(ξ - ζ5) * Q5^b * ξ^b - (1 - Q5*ξ) * (1 - κ5*Q5*ξ) * ξ^b for b in 0:2];
          [-(1 - Q5*ξ) * (1 - κ5*Q5*ξ) * (ξ*(1 - ζ5)*(1 - κ5*ζ5) - ξ + ζ5)]]
    A = [coeff(c, d) for d in 0:4, c in cs]
    ker = QuantumWZ.kernel_field(F5, A)
    @test size(A) == (5, 4) && length(ker) == 1
    @test [x * inv(ker[1][end]) for x in ker[1]] == [-ζ5, (1 + κ5)*ζ5, -κ5*ζ5, one(F5)]
end
