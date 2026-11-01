# §4.5: residues of parts at prescribed indices (Berkovich–Uncu, Fu–Zeng).
@isdefined(PAPER_DATA) || include("data.jl")

"(o(λ), e(λ)): odd parts at odd, resp. even indices of λ, given in decreasing order."
oddindices(λ) = (count(i -> isodd(λ[i]) && isodd(i), eachindex(λ)), count(i -> isodd(λ[i]) && iseven(i), eachindex(λ)))

"The numbers of parts ≡ 1 and ≡ 3 modulo 4."
residues4(λ) = (count(p -> mod(p, 4) == 1, λ), count(p -> mod(p, 4) == 3, λ))

"""
The system (42) at x = 1 for the two automata of §4.5, with u, v specialized to integers:
L = I − qR A_R − qΥ A_U, f = r₀, and C = qR d m.
"""
function bu_system(u::Integer, v::Integer)
    n = 16
    s1(h, k, r) = 4h + 2k + r + 1                   # (h, k, r) ∈ {0,1}³: first automaton
    s2(h, r) = 9 + 2mod(h, 4) + r                   # (h, r) ∈ ℤ/4 × {0,1}: second automaton
    w(h, k) = h == 0 ? 1 : (k == 1 ? u : v)
    wt(h) = h == 1 ? u : (h == 3 ? v : 1)
    AR, AU = zeros(Int, n, n), zeros(Int, n, n)     # an arc j → i adds its weight to entry (i, j)
    r0, d = zeros(Int, n), zeros(Int, n)
    for h in 0:1, k in 0:1
        for r in 0:1
            AR[s1(1 - h, k, 1), s1(h, k, r)] += 1
        end
        AU[s1(h, 1 - k, 0), s1(h, k, 1)] += w(h, k)
        k == 1 && (d[s1(h, 1, 1)] += w(h, 1))
    end
    r0[s1(1, 0, 1)] += 1
    r0[s1(1, 1, 1)] += 1
    for h in 0:3
        for r in 0:1
            AR[s2(h + 1, 1), s2(h, r)] += 1
        end
        AU[s2(h, 0), s2(h, 1)] += wt(h)
        d[s2(h, 1)] -= wt(h)
    end
    r0[s2(1, 1)] += 1
    L = [oper((Int(i == j), 0, 0), (-q * AR[i, j], 1, 0), (-q * AU[i, j], 0, 1)) for i in 1:n, j in 1:n]
    Problem((L, [oper((x, 0, 0)) for x in r0], [oper((q * x, 1, 0)) for x in d]))
end

@testset "§4.5: Berkovich–Uncu" begin
    # (41) to order q^N: (o, e) and the numbers of parts ≡ 1, 3 (mod 4) are equidistributed.
    N = 40
    stats(f) = sort([(sum(λ; init = 0), f(λ)...) for λ in distinct_partitions(N)])
    @test stats(oddindices) == stats(residues4)

    # The automata: at (u, v) = (2, 3) and (5, 7), b_n is the difference of the weighted counts of
    # the distinct partitions with largest part at most n; ν(b_n) ≥ n + 1.
    n = 8
    for (u, v) in ((2, 3), (5, 7))
        p = bu_system(u, v)
        b = bvalues(p, n)
        weight((i, j)) = K(u)^i * K(v)^j
        @test all(b[k+1] == sum((weight(oddindices(λ)) - weight(residues4(λ))) * q^sum(λ; init = 0)
                                for λ in distinct_bounded(k)) for k in 0:n)
        @test rate_ok(p, n)
    end

    # The recurrence (44), its solution (45), and the direct count with largest part at most 2N.
    poch(a, b, m) = prod((1 - a * b^j for j in 0:m-1); init = one(K))
    function T(M, i, j)
        (i < 0 || j < 0 || i + j > M) && return zero(K)
        q^(2i^2 - i + 2j^2 + j) * poch(q^4, q^4, M) * inv(poch(q^4, q^4, i) * poch(q^4, q^4, j) * poch(q^2, q^2, M - i - j))
    end
    E = Dict((0, 0) => one(K))
    e(D, i, j) = get(D, (i, j), zero(K))
    for M in 1:5
        E = Dict((i, j) => e(E, i, j) + q^(2M) * e(E, j, i) + q^(2M - 1) * e(E, j, i - 1) + q^(4M - 1) * e(E, i, j - 1)
                 for i in 0:M for j in 0:M-i)
        @test all(e(E, i, j) == T(M, i, j) for i in 0:M+1, j in 0:M+1)
        cnt = Dict{Tuple{Int,Int},elem_type(K)}()
        for λ in distinct_bounded(2M)
            cnt[oddindices(λ)] = get(cnt, oddindices(λ), zero(K)) + q^sum(λ; init = 0)
        end
        @test all(e(cnt, i, j) == T(M, i, j) for i in 0:M, j in 0:M)
    end

    # The polynomial identities (46) and (47).
    S, (X, Y, Z) = polynomial_ring(QQ, [:X, :Y, :Z])
    @test (Y*Z - X) * (Z + X*Y) + X*Z*(1 - Y^2) + X^2*Y*(1 - Z^2) == Y*Z^2*(1 - X^2)
    S2, (ii, jj) = polynomial_ring(QQ, [:i, :j])
    @test 2ii^2 - ii + 2jj^2 + jj - 2(ii + jj) + 1 == (ii - 1)*(2ii - 1) + jj*(2jj - 1)

    # Fu–Zeng: T^(L)_N of (51) satisfies (50), as polynomials in z, w over ℚ(q), for L = 2, 3, 4.
    Szw, (z, w) = polynomial_ring(K, [:z, :w])
    for Lm in 2:4
        TL(M, a, c) = q^(Lm*a*(a - 1) + Lm*c^2) * poch(q^(2Lm), q^(2Lm), M) *
            inv(poch(q^(2Lm), q^(2Lm), a) * poch(q^(2Lm), q^(2Lm), c) * poch(q^Lm, q^Lm, M - a - c))
        FN(M, x, y) = sum(TL(M, a, c) * x^a * y^c for a in 0:M for c in 0:M-a)
        @test FN(0, z, w) == one(Szw)
        @test all(FN(M, z, w) == (1 + q^(Lm*(2M - 1)) * w) * FN(M - 1, z, w) + q^(Lm*(M - 1)) * (q^Lm + z) * FN(M - 1, w, z)
                  for M in 1:4)
    end
end
