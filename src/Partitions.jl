module Partitions

__precompile__(false)

#using Debugger

include("qplane.jl")

using LightGraphs, Nauty, Distributed

include("automata.jl")

using GraphViz, URIs, HTTP, OpenFST, LLLplus

include("tools.jl")

euler1 = Automaton{2}([(1,1,2),(1,2,1),(2,1,1),(1,1,3)])
euler2 = Automaton{2}([(1,1,1),(1,2,2),(2,1,1),(1,1,3)])
euler3 = Automaton{4}([(1,2,1),(1,4,2),(2,1,1),(2,2,2),(3,4,1),(3,4,2),(4,3,1),((i,i,3) for i=[1,2,3])...])
euler4 = Automaton{5}([(1,3,1),(1,5,2),(2,1,1),(2,2,2),(3,4,1),(3,2,2),(4,5,2),(5,2,1),(1,1,3),(2,2,3),(3,3,3),(4,4,3)])

δ = simplify(quantumseries(euler2,order=[2,1])-quantumseries(euler1,order=[2,1]))

end
