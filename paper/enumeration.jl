# §3.8 and §4.6: exhaustive enumeration of small automata, and the families of equal series.
# Requires the enumerator: make -C exhaustivautomata.
# By default n = 4 (222354 automata). PARTITIONS_N=5 runs the search of §4.6: 14614080 automata,
# about 8 minutes for the enumerator alone, and enough memory to hold all of them with their series.
@isdefined(PAPER_DATA) || include("data.jl")

@testset "§3.8, §4.6: exhaustive enumeration" begin
    n = parse(Int, get(ENV, "PARTITIONS_N", "4"))
    area = n ≤ 4 ? 30 : 50
    families = filter(c -> length(c.first) > 1, cluster(allautomata(n; area = area)))
    println(length(families), " families of at least two automata with ≤ $n states and equal series to q^$area")
    i = findfirst(c -> c.second == growthseries(L_odd, area), families)       # Euler's identity
    @test i !== nothing && length(families[i].first) ≥ 2
    n ≥ 5 && @test any(c -> c.second == growthseries(L_A, area), families)    # the identity of §4.6
    # One line per family, in the input format of quantum-wz/automata_quantumwz.jl, which certifies
    # the differences within each family:
    file = joinpath(@__DIR__, "families$n.txt")
    open(io -> foreach(c -> println(io, c.first), families), file, "w")
    println("written to $file; certify with: julia --project=. quantum-wz/automata_quantumwz.jl $file")
end
