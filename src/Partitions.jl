module Partitions

__precompile__(false)

#using Debugger

include("qplane.jl"); using .QuantumPlane

using Nauty, Distributed

include("automata.jl")

using GraphViz, URIs, HTTP, OpenFST, LLLplus

include("tools.jl")

euler1 = Automaton{2}([(1,1,2),(1,2,1),(2,1,1),(1,1,3)])
euler2 = Automaton{2}([(1,1,1),(1,2,2),(2,1,1),(1,1,3)])
euler3 = Automaton{4}([(1,2,1),(1,4,2),(2,1,1),(2,2,2),(3,4,1),(3,4,2),(4,3,1),((i,i,3) for i=[1,2,3])...])
euler4 = Automaton{5}([(1,3,1),(1,5,2),(2,1,1),(2,2,2),(3,4,1),(3,2,2),(4,5,2),(5,2,1),(1,1,3),(2,2,3),(3,3,3),(4,4,3)])

# δ = simplify(quantumseries(euler2,order=[2,1])-quantumseries(euler1,order=[2,1]))

kr1 = Automaton{9}([((i,1+(i%9),1) for i=1:9)...,((i,i,s) for i=[1,3,6,8], s=2:3)...])
#q1 = quantumseries(kr1,order=[2,4,5,7,9,8,3,1,6])
#U⁺ = inv(1-U)
#q1 =  1+R*inv(1-U⁺*R^2*U⁺*R^3*U⁺*R^2*U⁺*R^2)*(1+U⁺*R^2*(1+U⁺*R^3*(1+U⁺*R^2)))*U⁺*U

kr2 = let x2v(i,j,a,b) = (3-i)*4*4*3 + (3-j)*4*3 + ((a+1)%4)*3 + (b+2)%3 + 1,
    kr2₀ = Automaton{4*4*4*3}([((x2v(i,j,a,b),x2v(i,min(j+1,3),a,(b+1)%3),1) for i=0:3, j=0:3, a=0:3, b=0:2)...,
                                      ((x2v(i,j,a,b),x2v(j,0,b,b),s) for i=0:3, j=0:3, a=0:3, b=0:2, s=2:3 if i+j≥3 && (a==3 || (j≤1) <= ((a+b)%3 == 0)))...])
    automaton(fst(kr2₀) |> determinize |> minimize)
end

#q2 = quantumseries(kr2,order=[6,7,8,10,11,14,4,5,9,12,13,1,2,3])


end
