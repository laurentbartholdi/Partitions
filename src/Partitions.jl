module Partitions

__precompile__(false)

#using Debugger

include("qplane.jl"); using .QuantumPlane

using LightGraphs, Nauty, Distributed

include("automata.jl")

using GraphViz, URIs, HTTP, OpenFST, LLLplus

include("tools.jl")

euler1 = Automaton{2}([(1,1,2),(1,2,1),(2,1,1),(1,1,3)])
euler2 = Automaton{2}([(1,1,1),(1,2,2),(2,1,1),(1,1,3)])
euler3 = Automaton{4}([(1,2,1),(1,4,2),(2,1,1),(2,2,2),(3,4,1),(3,4,2),(4,3,1),((i,i,3) for i=[1,2,3])...])
euler4 = Automaton{5}([(1,3,1),(1,5,2),(2,1,1),(2,2,2),(3,4,1),(3,2,2),(4,5,2),(5,2,1),(1,1,3),(2,2,3),(3,3,3),(4,4,3)])

δ = simplify(quantumseries(euler2,order=[2,1])-quantumseries(euler1,order=[2,1]))

kr1 = Automaton{9}([((i,1+(i%9),1) for i=1:9)...,((i,i,s) for i=[1,3,6,8], s=2:3)...])
#q1 = quantumseries(kr1,order=[2,4,5,7,9,8,3,1,6])
U⁺ = inv(1-U)
q1 =  1+R*inv(1-U⁺*R^2*U⁺*R^3*U⁺*R^2*U⁺*R^2)*(1+U⁺*R^2*(1+U⁺*R^3*(1+U⁺*R^2)))*U⁺*U

kr2 = let x2v(i,j,a,b) = (3-i)*4*4*3 + (3-j)*4*3 + ((a+1)%4)*3 + (b+2)%3 + 1,
    kr2₀ = Automaton{4*4*4*3}([((x2v(i,j,a,b),x2v(i,min(j+1,3),a,(b+1)%3),1) for i=0:3, j=0:3, a=0:3, b=0:2)...,
                                      ((x2v(i,j,a,b),x2v(j,0,b,b),s) for i=0:3, j=0:3, a=0:3, b=0:2, s=2:3 if i+j≥3 && (a==3 || (j≤1) <= ((a+b)%3 == 0)))...])
    automaton(fst(kr2₀) |> determinize |> minimize)
end

#q2 = quantumseries(kr2,order=[6,7,8,10,11,14,4,5,9,12,13,1,2,3])

bad_den = (-𝕢^32 - 𝕢^30)*U^6*R^9 + (-𝕢^27 - 𝕢^24 - 𝕢^22)*U^5*R^9 + (-𝕢^23 - 𝕢^21)*U^5*R^6 + (-𝕢^19)*U^4*R^9 + (-𝕢^19 - 2*𝕢^18 - 𝕢^16 - 𝕢^13)*U^4*R^6 + (-𝕢^14 - 𝕢^13 - 𝕢^11 - 2*𝕢^10 - 𝕢^8)*U^3*R^6 + (𝕢^14 + 𝕢^12 + 𝕢^11 + 𝕢^9)*U^3*R^3 + (-𝕢^6 - 𝕢^5)*U^2*R^6 + (𝕢^10 + 2*𝕢^9 + 𝕢^8 + 𝕢^7 + 𝕢^6 + 𝕢^4 + 𝕢^3)*U^2*R^3 + (𝕢^2 + 2*𝕢)*U*R^3 + (-𝕢^8 - 𝕢^6)*U - 1 |> numerator

bad_num = (-𝕢^31 - 𝕢^29)*U^6*R^9 + (-𝕢^26)*U^5*R^9 + (𝕢^22 + 𝕢^20)*U^5*R^8 + (-𝕢^22 - 𝕢^20)*U^5*R^7 + (𝕢^17)*U^4*R^8 + (-𝕢^17)*U^4*R^7 + (-𝕢^18 - 𝕢^16)*U^4*R^6 + (-𝕢^15 - 𝕢^13)*U^4*R^5 + (-𝕢^10)*U^3*R^6 + (𝕢^12)*U^3*R^5 + (-𝕢^12 - 𝕢^10)*U^3*R^4 + (𝕢^4)*U^2*R^5 + (-𝕢^4)*U^2*R^4 + (-𝕢^8 - 𝕢^6)*U^2*R^2 - U*R^2 |> numerator

"""sols: [19,21], [18,22], [17,23], [16,24], [15,25], *[14,28], *[13,33], [12,48], ..."""

end
