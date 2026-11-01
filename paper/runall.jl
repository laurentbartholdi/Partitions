# Reproduce the computations of §1 and §4 of the paper:  julia --project=. paper/runall.jl
# (The enumeration of §3.8 and §4.6 is separate: paper/enumeration.jl.)
include(joinpath(@__DIR__, "data.jl"))

@testset "Automatic partition identities" begin
    for f in ("euler.jl", "glaisher.jl", "primc.jl", "rogers_ramanujan.jl", "bessenrodt.jl",
              "berkovich_uncu.jl", "five_states.jl")
        include(joinpath(@__DIR__, f))
    end
end
