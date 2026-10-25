using Oscar, Test
include(joinpath(@__DIR__, "QuantumWZ.jl"))
using .QuantumWZ

ctx = setup()
(; t, Yo, T, O, A, X, Y, F, tF, zF) = ctx
o, Z = one(O), zero(O)
c(x) = O(x)                                     # scalar of K as an operator
tY, tT = c(t) * Yo, c(t) * T

# automata over {X, Y} (states 1..n); h − 1 = Y (Σ_w w) X, parts = number of Y's before each X
odd_aut   = automaton(ctx, 2, [(1, 1, X), (1, 2, Y), (2, 1, Y)], 1, [1])      # w ∈ {X, YY}*
dist_aut  = automaton(ctx, 2, [(1, 1, Y), (1, 2, X), (2, 1, Y)], 1, [1])      # w ∈ {Y, XY}*
odd_pbw   = (fill(one(A) - A(t) * X - A(t^2) * Y^2, 1, 1), [X], [A(t) * Y])
dist_pbw  = (fill(one(A) - A(t) * Y - A(t^2) * X * Y, 1, 1), [X], [A(t) * Y])
# a redundant (non-minimal) automaton for {Y, XY}*: state 3 duplicates state 1
dist_aut3 = automaton(ctx, 3, [(1, 1, Y), (1, 2, X), (2, 3, Y), (3, 3, Y), (3, 2, X)], 1, [1, 3])
# Glaisher (k = 3): parts not divisible by 3, and parts used at most twice
notdiv3 = automaton(ctx, 3, [(1, 2, Y), (2, 3, Y), (3, 1, Y), (2, 2, X), (3, 3, X)], 2, [2, 3])
mult3   = automaton(ctx, 3, [(1, 1, Y), (2, 1, Y), (3, 1, Y), (1, 2, X), (2, 3, X)], 1, [1, 2])

# Six operator forms (L, f, d) with the same S: partitions into distinct parts ≥ 2
six = [
  ([(o - tT) (-tT); (-tY) o],                         [o, Z],    [Z, tY]),
  ([o (-tT); (-tY) (o - tY)],                         [o, Z],    [Z, tY]),
  ([o (-tY); (-tT) (o - tT)],                         [o, Z],    [Z, tY]),
  ([o (-tY) Z; (-tY) o (-tY); (-tT) (-tT) o],         [o, Z, Z], [Z, tY, Z]),
  ([o (-tY) Z; (-tY) o (-tT); (-tT) (-tT) o],         [o, Z, Z], [Z, tY, Z]),
  ([o Z Z; Z (o - tY) (-tY); (-tT) (-tT) o],          [o, Z, Z], [Z, tY, tY]),
]

prove(R; kw...) = attempt(ctx, compile(ctx, R...)...; kw...)

@testset "QuantumWZ" begin
  @testset "basic cases" begin
    # X − Y = (1 − X)(−1) + 1·(1 − Y): a certificate without denominator
    r = attempt(ctx, x_minus_y(ctx)...)
    @test r.status == :proved && r.method == :rational && r.pole == 0 && r.κ == 0

    # β_n = t^(n+1)/(1 − t^(2n+1)) → 0: the certificate b = P·C needs the denominator
    # 1 + T², which has no pole at T = 0 (and no polynomial certificate of C exists)
    L = [o - tY Z; -c(t) o - c(t) * T^2]
    r = attempt(ctx, L, [o, Z], [Z, o - Yo])
    @test r.status == :proved && r.method == :rational && r.pole == 0
    @test any(QuantumWZ.zdeg(F(denominator(x))) > 0 for x in r.p)

    # Δ = 1: β_0 = 1 already exceeds the a-priori rate
    r = attempt(ctx, delta_one(ctx)...)
    @test r.status == :nonzero && r.n == 0 && r.valuation == 0

    # C = 0 identically, but no boundary certificate exists
    r = attempt(ctx, incomplete(ctx)...)
    @test r.status == :proved && r.method == :zero_marginal
  end

  @testset "equal series, different realizations" begin
    # decided by the annihilator: C ≡ 0
    L = [o - c(t) * Yo - c(t^2) * Yo * T   Z               Z;
         Z                                 o - c(t) * Yo   (-c(t) * Yo);
         Z                                 (-c(t) * T)     o]
    f = [o, o, Z]
    d = [c(t) * Yo, -c(t) * Yo, Z]
    r = attempt(ctx, L, f, d)
    @test r.status == :proved && r.method == :zero_marginal
    for (R1, R2) in [(dist_pbw, dist_aut), (odd_pbw, odd_aut), (dist_aut, dist_aut3)]
      @test prove(difference(R1, R2)).method == :zero_marginal
    end
  end

  @testset "Euler" begin
    # every rational certificate has a pole at T = 0 (an inverse shift): the limit
    # is a product identity, so the proof needs channels and a dilation witness
    for (R1, R2) in [(odd_pbw, dist_pbw), (odd_aut, dist_aut), (odd_pbw, dist_aut),
                     (odd_aut, dist_aut3)]
      r = prove(difference(R1, R2))
      @test r.status == :proved && r.method == :channels && r.period == 2
      @test [(p.kind, p.λ) for p in r.parts] == [(:dilation, 2)]
    end
    L, f, d = euler(ctx)
    @test L[1, 1] == o - c(t) * T - c(t^2) * Yo^2 && L[2, 2] == o - c(t) * Yo - c(t^2) * Yo * T
    @test attempt(ctx, L, f, -d).method == :channels
  end

  @testset "six forms of one series: all 15 differences" begin
    for i in 1:6, j in i+1:6
      r = attempt(ctx, difference(six[i], six[j])...)
      @test r.status == :proved
    end
    # the hardest pair needs a canonical reading and a shifted dilation witness
    r = attempt(ctx, difference(six[4], six[5])...)
    @test r.method == :channels && r.reading == ("cX'", "X")
    @test [(p.kind, p.λ, p.μ, p.χ) for p in r.parts] == [(:dilation, 2, 1, one(F) - tF^4 * zF^2)]
    # distinct parts ≥ 2 versus distinct parts ≥ 1: not an identity
    @test attempt(ctx, difference(six[1], compile(ctx, dist_aut...))...).status == :nonzero
    # input in plain notation: integer entries and scalars times operators
    plain1 = ([-t*T+1 -t*T; -t*Yo 1], [1, 0], [0, t*Yo])
    @test attempt(ctx, difference(plain1, six[2])...).status == :proved
  end

  @testset "least annihilator" begin
    # B1 − B3 of family B: in the readings (X, Y) the system gives an annihilator of
    # order 2, but the difference C is q-hypergeometric; the certificate for its
    # least annihilator (order 1) has no pole at T = 0
    B1 = ([o Z Z; (-tT) (o - tT) (-tY); (-tY) (-tY) o], [o, Z, Z], [Z, tY, Z])
    B3 = ([o Z Z; (-tY) (o - tY) (-tT); (-tT) (-tT) o], [o, Z, Z], [Z, tY, Z])
    r = attempt(ctx, difference(B1, B3)...)
    @test r.status == :proved && r.method == :rational && r.pole == 0 && r.κ == 0
    @test QuantumWZ.ydeg(r.annihilator) == 1
    # C3 − C5 of family C: the readings (X, Y) differ by the polynomial t − tY
    C3 = ([o Z Z; (-tT) (o - tT) (-tY); Z (-tY) o], [o, Z, Z], [tY, tY, Z])
    C5 = ([o Z Z; (-tT) (o - tY) (-tT); Z (-tT) o], [o, Z, Z], [tY, tY, Z])
    r = attempt(ctx, difference(C3, C5)...)
    @test r.status == :proved && r.method == :rational && QuantumWZ.ydeg(r.annihilator) == 0
  end

  @testset "automata in the R/U notation" begin
    # R = Y, U = X; 0 initial, ∞ final. Euler: odd parts versus distinct parts
    odd, dist = automaton(ctx, "0R1 1R2 1U1 1U∞ 2R1"), automaton(ctx, "0R1 1R1 1U2 2R1 1U∞")
    @test prove(difference(odd, dist)).status == :proved
    @test automata("Automaton[[0R1 1U1 1U∞], [0R1 1R1 1U∞]]") == ["0R1 1U1 1U∞", "0R1 1R1 1U∞"]
    # the two products differ by a boundary factor, (1 − t)(−t;t)_2m (t³;t²)_m =
    # (1 − t^(2m+1)) ∏_(l=m+1..2m) (1 − t^(2l)): the witness needs a shift Γ ≠ 1
    a1, a4 = automaton(ctx, "0R1 1U2 2R2 2U3 3R2 3U∞"), automaton(ctx, "0R1 1R2 2R3 3R2 3U3 3U∞")
    r = prove(difference(a1, a4))
    @test r.status == :proved && r.method == :channels
    @test any(p.kind == :dilation && !isone(p.Γ) for p in r.parts)
    # the second marginal of one automaton is the first marginal of the other, times Y
    b1, b2 = automaton(ctx, "0R1 1R2 1U3 2R3 2U1 3R1 3U2 3U∞"), automaton(ctx, "0R1 1R2 1U3 2R3 2U1 2U∞ 3R1 3U2")
    r = prove(difference(b1, b2))
    @test r.status == :proved && r.method == :zero_marginal && r.reading == ("X·Y^1", "Y")
  end

  @testset "a sum side: channels up to a remainder" begin
    # the β of a8 is not a sum of q-hypergeometric terms in any reading; at period 1
    # (reading Y) its adjoint recurrence has two q-hypergeometric solutions, and the
    # fit x = κ + G + (remainder → 0) needs a pole of order 1 at ζ = 0
    a7 = automaton(ctx, "0R1 1U2 2R3 2U4 3R2 3U4 3U∞ 4U3")
    a8 = automaton(ctx, "0R1 1U2 2R3 2U4 3R2 3U4 3U∞ 4R3")
    bd = QuantumWZ.block_reading(ctx, "Y", compile(ctx, a8...))
    els = QuantumWZ.hyper_elements(ctx, QuantumWZ.section_recurrence(ctx, bd.p, 1, 0))
    @test sort([string(e.ω) for e in els]) == sort(["t", "t^4*z + t"])
    ch = QuantumWZ.block_channels(ctx, bd, 1, 0, Dict{Int, Any}())
    @test !ch.exact && ch.pole == 1 && sort(string.(ch.ratios)) == ["1", "t^3*z + 1"]
    r = prove(difference(a7, a8))
    @test r.status == :proved && r.method == :channels && r.remainders == [:none, 1]
    @test [(p.kind, p.λ) for p in r.parts if p.kind == :dilation] == [(:dilation, 2)]
  end

  @testset "Glaisher, k = 3" begin
    r = prove(difference(notdiv3, mult3))
    @test r.status == :proved && r.method == :channels && r.period == 3
    @test any(p.kind == :dilation && p.λ == 3 for p in r.parts)
    # a false identity is refuted
    @test prove(difference(notdiv3, dist_aut)).status == :nonzero
  end
end
