# §4.1: Glaisher's identity (Proposition 4.1), through Corollary 3.8.
@isdefined(PAPER_DATA) || include("data.jl")

@testset "§4.1: Glaisher's identity" begin
    @test glaisher_nodiv(2) == L_odd && glaisher_mult(2) == L_distinct     # λ = 2 is Euler's identity
    F, (Q, Ug) = polynomial_ring(QQ, [:q, :U])
    Fr = fraction_field(F)
    N = 40
    for λ in 2:6
        H1, H2 = glaisher_nodiv(λ), glaisher_mult(λ)
        @test growthseries(H1, N) == growthseries(H2, N) == invprod([h for h in 1:N if h % λ != 0], N)

        # Proof of Proposition 4.1: θ = β/α, and χ(U) = 1 − q^λ U is a dilation witness, eq. (16) with ℓ = λ.
        α = prod(inv(Fr(1 - Q^i * Ug)) for i in 1:λ-1)
        β = prod(Fr(1 - Q^(λ*i) * Ug^λ) * inv(Fr(1 - Q^i * Ug)) for i in 1:λ)
        θ = β * inv(α)
        χ(x) = 1 - Q^λ * x
        @test θ * Fr(χ(Ug)) == Fr(prod(χ(Q^(λ*i) * Ug^λ) for i in 0:λ-1))

        # Corollary 3.8: b_(λk) = [R^(λk)](u_α − u_β) = Π_(j<k) α(q^(λj)) − Π_(j<k) β(q^(λj)),
        # read off the marginal system of H1 − H2; and ν(b_n) ≥ n + 1.
        αK(x) = prod((inv(1 - q^i * x) for i in 1:λ-1); init = one(K))
        βK(x) = prod(((1 - q^(λ*i) * x^λ) * inv(1 - q^i * x) for i in 1:λ); init = one(K))
        n = 3λ
        p = difference(compile(H1), compile(H2))
        b = bvalues(p, n)
        @test all(ν(b[k+1]) ≥ k + 1 for k in 0:n)
        @test all(b[λ*k+1] == prod((αK(q^(λ*j)) for j in 0:k-1); init = one(K)) -
                              prod((βK(q^(λ*j)) for j in 0:k-1); init = one(K)) for k in 0:3)
    end
end
