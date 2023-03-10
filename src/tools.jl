################################################################
# convert to FST, compute reverse (flip of partition)
const alphabet = Dict(:ϵ => 0, :R => 1, :U => 2)

"""Convert an Automaton to an OpenFST transducer"""
function fst(t::Automaton{N}) where {N}
    StdVectorFst(0,[(0,1,:R),((i,Int(t.x[i,s]),[:R,:U][s]) for i=1:N for s=1:2 if t.x[i,s]≠0)...,((i,N+1,:U) for i=1:N if t.x[i,3]≠0)...],[0,N+1],alphabet)
end

"""Convert and OpenFST transducer to an Automaton"""
function automaton(t::StdVectorFst)
    (init, arcs, final) = unpack(t |> determinize |> OpenFST.canonize!)
    @assert init == 0
    @assert count(a[1]==0 for a=arcs)==1
    @assert count(==((0,1,:R)),arcs)==1
    @assert all(p->(p[2]∈final)≤(p[3]==:U),arcs)
    prefinal = [i for (i,j,s)=arcs if s==:U && j∈final]
    M = numstates(t)
    Automaton{M-1}([((i,j,s==:R ? 1 : 2) for (i,j,s)=arcs if i≠0)...,((i,i,3) for (i,j,s)=arcs if s==:U && j∈final)...])
end

"""The automaton of all words read backwards with R,U exchanged"""
function reverse(t::Automaton{N}) where {N}
    automaton(fst(t * StdVectorFst(0,[(0,0,:R,:U),(0,0,:U,:R)],[0],alphabet)) |> reverse |> rmepsilon!)
end

const flipRU = StdVectorFst(0,[(0,0,:R,:U),(0,0,:U,:R)],[0],alphabet)
    
################################################################

export charpoly, degrees, series2pochhammer, growthseries

"""The characteristic polynomial of the transition matrix of t"""
function charpoly(t::Automaton{N}, R = PolynomialRing(ZZ,"x")[1]) where {N}
    m = zeros(Int,N,N)
    for i=1:N, s=1:2
        t.x[i,s]≠0 && (m[i,t.x[i,s]] += 1)
    end
    charpoly(R,MatrixSpace(ZZ,MatrixSpace(R,N,N)(m)))
end

"""The degrees of the irreducible factors of the characteristic polynomial of t"""
function degrees(t::Automaton, R = PolynomialRing(ZZ,"x")[1])
    d = Int[]
    for (f,n)=factor(charpoly(t,R))
        for _=1:n
            push!(d,degree(f))
        end
    end
    d
end

"""Convert (the beginning of a) power series s = ∑_{i≥0} s[i+1] t^i into
a product ∏_{i≥1} (1+t^i)^p[i]"""
function series2product(s::Vector)
    s = copy(s)
    p = Int[]
    for i=1:length(s)-1
        push!(p,s[i+1])
        s[i+1:end] -= s[i+1]*s[1:end-i]
    end
    p
end

"""Convert a product series ∏_{i≥1} (1+t^i)^p[i] into a product of
Pochhammer symbols needed for p.
Symbol (a*q^i; q^k) = ∏_{j≥0} (1+a q^{i+kj}) is weighted k."""
function product2pochhammer(p::Vector{T},maxi=length(p)÷2) where {T}
    n = length(p)
    nc = maxi*(maxi-1)÷2
    mat = zeros(T,n+nc+1,1+nc)
    mat[1:n,1] = 1000p
    mat[n+nc+1,1] = 1
    c = 1
    indices = Tuple{Int,Int}[]
    for i=1:maxi, j=1:i-1
        mat[1:n,c+1] = [1000*Int(k%i == j) for k=1:n]
        mat[n+c,c+1] = 3(maxi+i)+j
        push!(indices,(i,j))
        c += 1
    end
    lmat,_,_ = lll(mat)
    ps = Tuple{Int,Int,Int}[]
    k = 1; while lmat[n+nc+1,k]==0
        k += 1
        k > size(lmat,2) && return :fail
    end
    for i=1:n
        lmat[i,k]≠0 && return :fail
    end
    for c=1:nc
        if lmat[n+c,k]≠0
            (i,j) = indices[c]
            push!(ps,(-lmat[n+c,k]/mat[n+c,c+1]/lmat[n+nc+1,k],j,i))
        end
    end
    ps  
end

"""Convert a power series into a product of Pochhammer symbols"""
series2pochhammer(s) = series2product(s) |> product2pochhammer

function growthseries_helper(t::Automaton{N}, area, counts, x, state) where {N}
    area ≥ x || return counts
    if t.x[state,1]≠0
        growthseries_helper(t, area, counts, x+1, t.x[state,1])
    end
    if t.x[state,2]≠0
        growthseries_helper(t, area-x, counts, x, t.x[state,2])
    end
    if t.x[state,3]≠0
        counts[area-x+1] += 1
    end
    counts
end

"""Compute the power series, up to q^area, of the growth of the automaton t"""
growthseries(t::Automaton, area) = [1; reverse!(growthseries_helper(t, area, zeros(Int,area), 1, 1))...]

################################################################

#export R, U, 𝕢, quantumseries, Polynomial, Fraction, RFraction, LFraction, simplify, cancel
export quantumseries, RFraction, LFraction, simplify, cancel

const R = QuantumPlane.Fraction(QuantumPlane.R)
const U = QuantumPlane.Fraction(QuantumPlane.U)

#const Polynomial = QuantumPlane.Polynomial
#const Fraction = QuantumPlane.Fraction
const RFraction = QuantumPlane.Fraction{:right}
const LFraction = QuantumPlane.Fraction{:left}
const simplify = QuantumPlane.simplify
#const 𝕢 = QuantumPlane.𝕢

"""Compute the rational expression in R,U expressing the automaton t."""
function quantumseries(t::Automaton{N}; order = 1:N) where N
    sort(order)==1:N || error("$order does not contain all states 1:$N")

    mat = fill(zero(R),N+2,N+2)
    mat[1,N+2] += one(R)
    mat[1,2] = R
    for i=1:N, c=1:3
        if t.x[i,c]≠0
            mat[i+1,c==3 ? N+2 : t.x[i,c]+1] += [R,U,U][c]
        end
    end
    for i=1:N # eliminate state order[i]
        si = order[i]+1
        loopi = inv(one(R)-mat[si,si])
        for j=1:N+2, k=1:N+2
            (j-1∈order[1:i] || k-1∈order[1:i]) && continue
            global stash
            stash = (mat[j,k],mat[j,si],loopi,mat[si,k])
            @info "(j,k)=($j,$k); computing $(mat[j,k]) += $(mat[j,si])*$loopi*$(mat[si,k])..."
            mat[j,k] += simplify(mat[j,si] * loopi * mat[si,k])
        end
    end
    mat[1,N+2]
end

function cancel(x,side)
    side∈[:left,:right] || error("$side should be :left or :right")

    x = convert(Fraction{side},x)
    if side==:left
        denominator(x) \ divrem(numerator(x),numerator(R-1),:left).remainder
    else
        divrem(numerator(x),numerator(U-1),:right).remainder / denominator(x)
    end
end

################################################################

export cluster, examine

"""Combine results of runs of scan"""
function cluster(scanresult::Vector{Pair{A,B}}) where {A,B}
    sort!(scanresult,lt=(x,y)->x.second<y.second)
    c = Pair{Vector{A},B}[]
    for (a,b)=scanresult
        if isempty(c) || c[end].second≠b
            push!(c,[a]=>b)
        else
            push!(c[end].first,a)
        end
    end
    c
end

"""Examine a row produced by cluster, pulling up data from OEIS"""
function examine(row)
    for g=row.first
        display(g)
    end
    println(row.second)
    html = String(HTTP.request("GET",string(URI(URI("https://oeis.org/search"); query=Dict("q"=>join(row.second |> string))))))
    htmlbuf = IOBuffer(html)
    mdbuf = IOBuffer()
    run(pipeline(`pandoc --from html --to markdown`, stdin=htmlbuf, stdout=mdbuf))
    seekstart(mdbuf)
    md = readlines(mdbuf)
    start = 1; while start < length(md) && match(r"^\[A.*\]\(/A.*\)$",md[start])==nothing start += 1 end
    display("text/markdown", join(md[start:end],"\n"))
end

"""
example:
[0R1 1R2 1U1 1U∞ 2R3 2U1 2U∞ 3R3 3U∞]
series:
((R - 1)*(q^2*U*R + q*U - 1)) \\ (q^3*U*R^2 + q*U*R - q*U - R + 1)

[0R1 1R2 1U1 1U∞ 2R2 2U3 2U∞ 3R2 3U∞]
series:
((q^2*U*R + R - 1)*(q*U - 1)) \\ (q^4*U^2*R + q*U*R - q*U - R + 1)


num den^-1 = x^-1 y: need x*num = y*den, llcm
num^-1 den = x y^-1: need num*x = den*y, rlcm

difference: 
"""
