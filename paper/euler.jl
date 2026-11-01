# §1 and Corollary 4.2: Euler's identity, from the automata to the certificate.
@isdefined(PAPER_DATA) || include("data.jl")

@testset "§1, Corollary 4.2: Euler's identity" begin
    # The languages L_o = R(U+RR)*U and L_d = R(R+UR)*U count the same partitions of each size.
    N = 60
    @test growthseries(L_odd, N) == growthseries(L_distinct, N) == invprod(1:2:N, N)
    @test spec(L_odd) == "0R1 1R2 1U1 1U∞ 2R1"
    @test pathseries(spec(L_odd), N)[2:end] == growthseries(L_odd, N)[2:end]
    # Their path series H_o, H_d as rational expressions in the quantum plane:
    println("H_o = ", quantumseries(L_odd), "\nH_d = ", quantumseries(L_distinct))

    # Normalized realizations and marginal systems, eqs. (8)–(9). Eliminating the second state gives
    # the operators of §1 at x = 1: (1 − qΥ − q²R²) m_o = 1 and (1 − qR − q²RΥ) m_d = 1; these are
    # also the 1×1 systems compiled from the regular expressions.
    po, pd = compile(L_odd), compile(L_distinct)
    Po, Pd = oper((1,0,0), (-q,0,1), (-q^2,2,0)), oper((1,0,0), (-q,1,0), (-q^2,1,1))
    @test po.L == compile(spec(L_odd)).L
    @test po.L[1,1] - po.L[1,2] * po.L[2,1] == Po
    @test pd.L[1,1] - pd.L[1,2] * pd.L[2,1] == Pd
    @test Partitions.euler_odd().L == fill(Po, 1, 1) && Partitions.euler_distinct().L == fill(Pd, 1, 1)

    # The canonical boundary b of S = H_o − H_d, eq. (11): b_n is the difference of the counts of the
    # partitions with largest part at most n, and ν(b_n) ≥ n + 1 (Theorem A(3)).
    n = 14
    p = difference(po, pd)
    b = bvalues(p, n)
    @test b == bvalues(difference(Partitions.euler_odd(), Partitions.euler_distinct()), n)
    @test all(b[k+1] == prod((inv(1 - q^j) for j in 1:2:k); init = one(K)) -
                        prod((1 + q^j for j in 1:k); init = one(K)) for k in 0:n)
    @test rate_ok(p, n)

    # Corollary 4.2, coefficientwise to R^n. The first-order series u, v of §1 have coefficients
    # u_k, v_k at R^(2k); the states m_(o,1), m_(d,1) of the system are Υ(1 − qΥ)⁻¹u and Υ B_d,
    # b = B_o − B_d (eq. (2)), u − v = q²Υψ, and b = qΥb' with b' ∈ ℚ[[q,R]].
    u(k) = k < 0 || isodd(k) ? zero(K) : prod((inv(1 - q^j) for j in 1:2:k-1); init = one(K))
    v(k) = k < 0 || isodd(k) ? zero(K) : prod((1 + q^j for j in 1:k); init = one(K))
    ψ(k) = k < 0 ? zero(K) : (u(k) - v(k)) * inv(q^(k + 2))
    Bo(k) = u(k) + (k ≥ 1 ? u(k - 1) * inv(1 - q^k) : zero(K))        # (1 + R(1 − qΥ)⁻¹)u
    Bd(k) = v(k) + (k ≥ 1 ? (1 + q^k) * v(k - 1) : zero(K))           # (1 + R(1 + qΥ))v
    b′(k) = q * ψ(k) + (k ≥ 1 ? (ψ(k - 1) + q^(k - 1) * v(k - 1)) * inv(1 - q^k) : zero(K))
    m = solvesystem(p, n)                  # states: m_(o,1), m_(o,2), m_(d,1), m_(d,2)
    @test all(m[1][k+1] == q^k * u(k) * inv(1 - q^(k + 1)) for k in 0:n)
    @test all(m[3][k+1] == q^k * Bd(k) for k in 0:n)
    @test all(b[k+1] == Bo(k) - Bd(k) for k in 0:n)
    @test all(ν(u(k) - v(k)) ≥ k + 2 for k in 0:n)
    @test all(b[k+1] == q^(k + 1) * b′(k) && ν(b′(k)) ≥ 0 for k in 0:n)
    # The polynomial identity behind v_k = u_k Π_(i=k+1)^(2k) (1 − q^(2i)):
    Rq, (Q, Ug) = polynomial_ring(QQ, [:q, :U])
    @test (1 - Q*Ug) * (1 + Q*Ug) * (1 + Q^2*Ug) * (1 - Q^2*Ug) == (1 - Q^2*Ug^2) * (1 - Q^4*Ug^2)

    # The certificate search of the implementation (§3.8, Appendix A) on the same difference:
    r = attempt(p)
    println("attempt: ", r.status, " ", get(r, :method, ""))
    @test r.status == :proved
end
