include("../quantum-wz/QuantumWZ.jl")

# X = U, Y = R

const qwzctx = QuantumWZ.setup() # move to __init__()

const Problem = @NamedTuple begin
    L::Matrix
    f::Vector
    d::Vector
end

attempt(p::Problem; N=24) = QuantumWZ.attempt(qwzctx, p.L, p.f, p.d; N = N)

function compile(t::Automaton{N})::Problem where N
    z = QuantumWZ.operator(qwzctx,[])
    o = z+1
    Y = qwzctx.Yo*qwzctx.t
    T = qwzctx.T*qwzctx.t
    L = [i == j ? o : z for i=1:N, j=1:N]
    f = [i == 1 ? o : z for i=1:N]
    d = [iszero(t.x[i,3]) ? z : Y for i=1:N]

    for i=1:N, s=1:2
        if !iszero(t.x[i,s])
            L[t.x[i,s],i] -= (s == 1 ? Y : T)
        end
    end
    
    (L = L, f, d)
end

function difference(p₁,p₂)::Problem
    o = QuantumWZ.operator(qwzctx,[])
    N₁ = length(p₁.f)
    N₂ = length(p₂.f)
   
    L = [o for i=1:N₁+N₂, j=1:N₁+N₂]
    L[1:N₁,1:N₁] = p₁.L
    L[N₁+1:N₁+N₂,N₁+1:N₁+N₂] = p₂.L
    
    (L = L, f = [p₁.f;p₂.f], d = [p₁.d;-p₂.d])
end
    
compile(t::Automaton{M},u::Automaton{N}) where {M,N} = difference(compile(t),compile(u))

# system is described in the form r*Q⁻¹*e with r,Q,e defined over X,Y.
# QuantumWZ.compile turns it into operator form (L,f,d) with
# L = Φ(Q'), f = ρ(r), d = Φ(e), for the maps Φ(X^a Y^b) = Y^b T^a, ρ(X^a Y^b) = Y^b

# euler_odd is: R(1-U-RR)⁻¹U, rewritten U(1-tU-t²RR)⁻¹tR = X(1-tX-t²Y²)tY
# compiled to L=[1-tT-t²Y²], f=[1], d=[tY]
function euler_odd()
    (; t, A, X, Y) = qwzctx
    QuantumWZ.compile(qwzctx, [one(A) - A(t) * X - A(t^2) * Y^2], [X], [A(t) * Y]) |> Problem
end

function euler_distinct()
    (; t, A, X, Y) = qwzctx
    QuantumWZ.compile(qwzctx, [one(A) - A(t) * Y - A(t^2) * X * Y], [X], [A(t) * Y]) |> Problem
end
