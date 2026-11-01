# §4.4: Bessenrodt's refinement of Euler's identity by the alternating sum α(λ).
@isdefined(PAPER_DATA) || include("data.jl")

"""
The system of §4.4 for S = H^z_d − H^z_o, with the statistic variable z specialized to an integer:
L = diag(L_d, 1 − zqΥ − q²R²), f = (0, 0, q, zq, q), d = (0, 0, 0, R, −zR).
"""
function bessenrodt_system(z::Integer)
    L = [O1 O0 O0 oper((-q,0,1)) O0;
         O0 O1 oper((-q,0,1)) O0 O0;
         oper((-q,1,0)) O0 oper((1,0,0), (-q,1,0)) O0 O0;
         O0 oper((-z*q,1,0)) O0 oper((1,0,0), (-z*q,1,0)) O0;
         O0 O0 O0 O0 oper((1,0,0), (-z*q,0,1), (-q^2,2,0))]
    Problem((L, [O0, O0, oper((q,0,0)), oper((z*q,0,0)), oper((q,0,0))], [O0, O0, O0, oper((1,1,0)), oper((-z,1,0))]))
end

@testset "§4.4: alternating sums" begin
    # (38) to order q^N: distinct partitions by z^α(λ), odd partitions by z^ℓ(μ), and 1/(zq; q²)_∞.
    N = 30
    dist = zeros(Int, N + 1, N + 1)                   # dist[n+1, k+1]: distinct λ ⊢ n with α(λ) = k
    for λ in distinct_partitions(N)
        dist[sum(λ; init = 0) + 1, altsum(λ) + 1] += 1
    end
    odd = zeros(Int, N + 1, N + 1)                    # Π_(j odd) 1/(1 − z q^j): odd μ ⊢ n with k parts
    odd[1, 1] = 1
    for j in 1:2:N, n in j:N, k in 1:N
        odd[n+1, k+1] += odd[n-j+1, k]
    end
    @test dist == odd

    # The telescoping certificate (40), in ℚ(η, Q, ξ).
    S, (e0, Q0, x0) = polynomial_ring(QQ, [:η, :Q, :ξ])
    F = fraction_field(S)
    η, Qv, ξ = F(e0), F(Q0), F(x0)
    r(x) = η * x^2 * inv((1 - Qv*x) * (1 - η*x))
    s(x) = x * (1 - η) * inv(1 - η*x)
    Ψ(x) = (1 - η) * (x - 1)
    @test r(ξ) * Ψ(Qv*ξ) - Ψ(ξ) == (1 - η) - s(ξ)

    # The quantum-plane data, at z = 2 and z = 3: the initial values m(0), and b_n equal to the
    # difference of the weighted counts with largest part at most n; ν(b_n) ≥ n + 1.
    n = 9
    for z in (2, 3)
        p = bessenrodt_system(z)
        m = solvesystem(p, 0)
        @test [m[i][1] for i in 1:5] == [z*q^2, q^2, q, z*q, q * inv(1 - z*q)]
        b = bvalues(p, n)
        @test all(b[k+1] == sum(K(z)^altsum(λ) * q^sum(λ; init = 0) for λ in distinct_bounded(k)) -
                            prod((inv(1 - z*q^j) for j in 1:2:k); init = one(K)) for k in 0:n)
        @test rate_ok(p, n)
    end
end
