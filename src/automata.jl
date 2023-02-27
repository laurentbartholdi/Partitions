################################################################
# produce automata generating partitions

export ScanData, scan, parallel_scan, Automaton

const LASTGEN = 3 # could be 2 to force acceptance precisely on U transitions

"""
The main data structure: Automaton.x[i,s] is the transition from state i on input s∈{1,2}; value 0 indicates no transition. There is implicitly an edge from the (unrepresented) initial state to 1 labeled 1. State i is accepting with implicit transition 2 iff Automaton.x[i,3]=1. Implicitly the empty word is also accepted.
Automaton.g is a copy of the data in the form of a Nauty graph.
"""
mutable struct Automaton{N}
    x::Array{UInt8,2}
    g::DenseNautyDiGraph

    function Automaton{N}(arcs::Vector = []) where {N}
        t = new(fill(UInt8(0),N,3))
        t.g = graph(t)
        for (i,j,s)=arcs
            add_arc!(t,i,j,s)
        end
        t
    end

    Automaton{N}(x,g) where {N} = new(x,g)
end
Base.copy(t::Automaton) = typeof(t)(copy(t.x),copy(t.g))
Base.:(==)(t::Automaton, u::Automaton) = t.x == u.x
Base.hash(t::Automaton) = hash(t.x)

partition(x::Automaton{N}) where {N} = (Vector{Cint}(0:3N-1),Vector{Cint}([1<i<N for _=1:3 for i=1:N]))

    
function add_arc!(t::Automaton{N}, i, j, s) where {N}
    t.x[i,s]==0 || return false
    t.x[i,s] = j

    add_edge!(t.g,i+(s-1)*N,j+(s-1)*N)

    s==2==LASTGEN && add_arc!(t, i, i, 3)

    return true
end

function rem_arc!(t::Automaton{N}, i, j, s) where {N}
    t.x[i,s] = 0

    s==2==LASTGEN && rem_arc!(t, i, i, 3)
    
    rem_edge!(t.g,i+(s-1)*N,j+(s-1)*N)
end

function Base.show(io::IO, m::MIME"image/svg+xml", t::Automaton{N}) where {N}
    buffer = IOBuffer()
    println(buffer, """digraph Automaton {
0 [shape=box,style=dashed]
∞ [shape=box,style=dashed]
0 -> 1 [color=blue,label=R]""")
    for i=1:N
        println(buffer, "$i [shape=box]")
    end
    for i=1:N, s=1:3
        t.x[i,s]≠0 || continue
            println(buffer,"$i -> $(s≤2 ? t.x[i,s] : '∞') [color=$(["blue","red","red"][s]),label=$("RUU"[s])]")
    end
    println(buffer, "}")
    seekstart(buffer)
    g = GraphViz.load(buffer)
    show(io, m, g)
end

function Base.show(io::IO, t::Automaton{N}) where {N}
    print(io,"[0R1")
    for i=1:N, s=1:3
        t.x[i,s]≠0 || continue
        print(io, " ", i, "RUU"[s], s≤2 ? t.x[i,s] : '∞')
    end
    print(io,"]")
end

"""
Convert a table to a graph, for canonization by Nauty
"""
function graph(t::Automaton{N}) where {N}
    g = DenseNautyDiGraph(3N)
    for i=1:N
        add_edge!(g,i,i+N)
        add_edge!(g,i+N,i+2N)
        for s=1:3
            t.x[i,s]≠0 && add_edge!(g,i+(s-1)*N,t.x[i,s]+(s-1)*N)
        end
    end
    g
end
const nautyopt = Nauty.DEFAULTOPTIONS_DIGRAPH()
nautyopt.defaultptn = 0
nautyopt.getcanon = 1

################################################################
# detect if automaton is minimal.

# count number of states reachable from "state" and not in "seen"
function reachable(t,seen,state)
    seen[state] && return 0
    seen[state] = true
    count = 1
    for s=1:2
        t.x[state,s]≠0 && (count += reachable(t,seen,t.x[state,s]))
    end
    count
end

# test if "state" leads to the accepting state
function coreachable(t,seen,state)
    seen[state] && return false # in loop
    seen[state] = true
    t.x[state,3]≠0 && return true
    for s=1:2
        t.x[state,s]≠0 && coreachable(t,seen,t.x[state,s]) && return true
    end
    return false
end

function collapsible(t::Automaton,seen,i,j)
    seen[i,j] && return true
    seen[i,j] = true
    for s=1:3
        (t.x[i,s]==0) ≠ (t.x[j,s]==0) && return false
    end
    c = true
    for s=1:2
        c &= (t.x[i,s]==0 || collapsible(t,seen,t.x[i,s],t.x[j,s]))
    end
    c
end

function minimal(t::Automaton{N}) where {N}
    # if there's a state with no output, NO
    for i=1:N
        if t.x[i,1]==t.x[i,2]==t.x[i,3]==0
            return false
        end
    end
    
    # if there's an unreachable state, NO
    reachable(t,falses(N),1) < N && return false

    # if there's a state that doesn't go to accept, NO
    for i=1:N
        coreachable(t,falses(N),i) || return false
    end
    
    # if two states act in the same way, NO
    for i=1:N, j=i+1:N
        collapsible(t,falses(N,N),i,j) && return false
    end
    
    true
end

################################################################
# enumeration of automata, now.
mutable struct ScanData
    level::Int # at which level in the recursion are we?
    split::Int # at which level do we separate between workers?
    numtables::Int # how many tables did we see at split level?
    dowork::Function # how do we determine, from numtables, whether to work?
    area::Int # how far we compute the areas
    debug::Bool
end
ScanData(area::Int) = ScanData(-2,-1,0,x->true,area,false)

"""
Canonical enumeration of tables.

Loosely based on McKay, "Isomorph-free exhaustive generation", DOI:10.1006/jagm.1997.0898

x is an empty table, to be filled in recursively
sd is a bunch of parameters determining when to split the recursion across cores, and how deep to search for periodicity / finiteness
candidates is the array to be filled in with the results
saveall specifies whether all periodicity tests should be saved, or not
"""
function scan(x::Automaton{N},sd::ScanData = ScanData(30),candidates::Vector{Pair{Automaton{N},Any}} = Pair{Automaton{N},Any}[],saveall = true) where {N}
    if sd.level==sd.split
        sd.numtables += 1
        sd.dowork(sd.numtables) || return candidates
    end

    minimal(x) && push!(candidates, copy(x)=>growthseries(x,sd.area))

    sd.debug && @info "$(repeat(".. ",3-sd.level)) Main scan, $x"

    sd.level == 0 && return candidates
    
    sd.level -= 1

    c = DenseNautyDiGraph[]

    for i=1:N, j=1:N, s=1:LASTGEN # add an edge from i to j labeled s
        s==3 && i≠j && continue # color 3 is just accepting
        add_arc!(x,i,j,s) || continue

        (_,orbits,lab,canong) = Nauty.densenauty(x.g, nautyopt, partition(x))

        # we now have a canonical labelling of g.
        # orbits[v] is the orbit representative of vertex v
        # lab[v]=w means that vertex w goes to position v in canong

        # find the "canonical edge" of canong; we take the first
        canono = -1
        for v=1:3N, w=1:3N
            if has_edge(canong,v,w) && lab[v]÷N == lab[w]÷N
                canono = orbits[lab[v]+1] # +1 because of C conventions in Nauty
                break
            end
        end
        sd.debug && @info "$(repeat(".. ",3-sd.level)) Trying $i$("RUU"[s])$(s==3 ? "∞" : j), canon=$canonedge, orbits=$orbits, lab=$lab"
        # if the canonical edge is in the same orbit as the added edge, proceed
        if canono == orbits[i+(s-1)*N] && all(x->x≠canong,c)
            push!(c,canong)
            scan(x,sd,candidates,saveall)
        end

        rem_arc!(x,i,j,s)
    end

    sd.level += 1
    sd.debug && @info "$(repeat(".. ",3-sd.level)) Out of main scan $x"
    return candidates
end

function parallel_scan(N,workers = nworkers(), area = 30)
    refs = [@spawnat :any scan(Automaton{N}(),ScanData(-2,-4,0,x->(x%workers==i-1),area,false),Pair{Automaton{N},Any}[],true) for i=1:workers]

    vcat(fetch.(refs)...)
end
