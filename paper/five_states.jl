# §4.6: an identity between five-state languages, with its direct certificate.
@isdefined(PAPER_DATA) || include("data.jl")

@testset "§4.6: five-state languages" begin
    N = 60
    @test growthseries(L_A, N) == growthseries(L_B, N)

    # L_B_conjugate accepts the reversed words of L_B with R and U interchanged (conjugate partitions):
    flip(w) = join(c == 'R' ? 'U' : 'R' for c in reverse(w))
    words = [join(isodd(m >> k) ? 'U' : 'R' for k in 0:n-1) for n in 1:12 for m in 0:2^n-1]
    @test all(npaths(spec(L_B), w) == npaths(L_B_conjugate, flip(w)) for w in words)
    @test pathseries(L_B_conjugate, N)[2:end] == growthseries(L_B, N)[2:end]

    # The kernel (54): the systems compiled from the incoming arcs of L_A (m) and of L_B_conjugate (c).
    qR, qΥ = oper((q,1,0)), oper((q,0,1))
    system(n, off) = [i == j ? O1 : -get(off, (i, j), O0) for i in 1:n, j in 1:n]
    pA, pB = compile(L_A), compile(L_B_conjugate)
    @test pA.L == compile(spec(L_A)).L ==
          system(5, Dict((1,3) => qΥ, (2,1) => qR, (3,2) => qΥ, (3,4) => qΥ, (4,3) => qR, (4,5) => qΥ, (5,4) => qR))
    @test pA.f == [O1, O0, O0, O0, O0] && pA.d == [O0, qR, qR, qR, qR]
    @test pB.L == system(5, Dict((1,2) => qΥ, (2,1) => qR, (2,3) => qΥ, (3,2) => qR, (3,4) => qΥ, (4,5) => qR, (5,3) => qΥ))
    @test pB.f == [O0, O1, O0, O1, O0] && pB.d == [qR, O0, O0, O0, O0]

    # The operators (56) and those of the verification, and the exact identities in 𝒪.
    P = oper((1,0,0), (-q^2*(1+q),1,1), (-q^3,1,2), (q^8,2,3))
    Qo = oper((-1,0,0), (-(1+q),1,0), (-1,2,0), (q*(q^2-1),1,1), (q^5,2,2))
    Θ = oper((1,1,0), (q,1,1), (-q^3,2,1), (q^3,3,1), (-q^5,2,2))
    Ω = oper((1,0,0), (-q*(1+q),1,1), (-q^4,1,2), (q^6,2,3))
    Nop = oper((q,0,0), (q*(1+q),1,0), (q^2,0,1), (q^2,1,1), (-q^6,1,2), (-q^6,2,2))
    J = oper((q,0,0), (q*(1+q),1,0), (q^2,0,1), (q^4,1,1), (-q^3,1,2), (-q^6,2,2))
    X = oper((1,0,1), (-q^5,1,3))                 # Υ − q⁵RΥ³
    W = oper((1,1,0), (-q^2,0,2), (-q^5,1,2))     # R − q²(1 + q³R)Υ²
    # q²R m_i = V_i ψ solves the m-equations of (54) at x = 1 when Pψ = q²R:
    V = [oper((1,0,0), (-q^2*(1+q),1,1)), oper((q,1,0), (-q^3*(1+q),2,1)), oper((q^2,1,1), (-q^6,2,2)),
         oper((q^3,2,1)), oper((q^4,3,1))]
    @test V[1] - Υ * V[3] == P
    @test V[2] == qR * V[1] && V[3] == Υ * (V[2] + V[4]) && V[4] == qR * V[3] + Υ * V[5] && V[5] == qR * V[4]
    @test oper((q,0,0)) * Θ == V[2] + V[3] + V[4] + V[5]                                 # (58), first line
    @test Ω * Nop == J * P                                                              # (59)
    @test act(Ω, oper((q,0,0), (q,1,0))) + act(J, oper((q^2,1,0))) == oper((q,0,0), (q - q^2,1,0))
    @test Θ - X * Nop - (O1 - R) * qΥ * Qo == W * P                                   # (60)
    @test oper((q,0,0)) - act(X, oper((q,0,0), (q,1,0))) + (O1 - R) * oper((q^2,1,0)) +
          act(W, oper((q^2,1,0))) == O0

    # The same statements on the series, to order R^n: ψ ∈ ℤ[q][[R]], the states of (54), the
    # elimination (58), c₃ = q(1 + R) + Nψ, and b = qΥφ with φ = Qψ − R (eq. (57)).
    n = 12
    ψ = QuantumWZ.solve_series(ctx, fill(P, 1, 1), [oper((q^2,1,0))], n)[1]
    @test all(inZq, ψ)
    m, c = solvesystem(pA, n), solvesystem(pB, n)
    @test all(coeff_R(V[i], ψ, k) == coeff_R(oper((q^2,1,0)), m[i], k) for i in 1:5, k in 0:n)
    @test all(coeff_R(Ω, c[3], k) == coeff_R(oper((q,0,0), (q - q^2,1,0)), [one(K)], k) for k in 0:n)
    @test all(coeff_R(qR, c[1], k) == coeff_R(X, c[3], k) - (k == 0 ? q : zero(K)) for k in 0:n)
    @test all(c[3][k+1] == coeff_R(Nop, ψ, k) + coeff_R(oper((q,0,0), (q,1,0)), [one(K)], k) for k in 0:n)
    φ = [coeff_R(Qo, ψ, k) - (k == 1 ? one(K) : zero(K)) for k in 0:n]
    @test all(inZq, φ)
    p = difference(pA, pB)
    @test bvalues(p, n) == [coeff_R(qΥ, φ, k) for k in 0:n]
    @test rate_ok(p, n)

    # The certificate search of the implementation on L_A − L_B (§3.8, Appendix A):
    r = attempt(difference(pA, compile(L_B)); time_limit = 300)
    println("attempt: ", r.status, " ", get(r, :method, ""))
    @test r.status != :nonzero
end
