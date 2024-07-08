module QuantumPlane

using Oscar, DataStructures, Test

const run_tests = true

export Polynomial, Fraction, 𝕢, R, U, simplify, series

const ℚ𝕢, 𝕢 = rational_function_field(QQ,:𝕢)
const Scalar = typeof(𝕢)
const 𝔸, (U, R) = let (A, (U, R)) = ℚ𝕢["U","R"]
    pbw_algebra(A, strictly_upper_triangular_matrix([𝕢*U*R]), deglex(A))
end
const Polynomial = typeof(U)
const Exponent = Vector{Int}
const ℚ𝕢X,X = polynomial_ring(ℚ𝕢,:X)

# seem missing
Base.zero(::Type{Scalar}) = zero(𝕢)
Base.one(::Type{Scalar}) = one(𝕢)
Oscar.coefficients_and_exponents(p::Polynomial) = zip(coefficients(p),exponents(p))

if false
using MagmaCall
# magma interface for ℚ𝕢
const magma_ℚ𝕢, magma_𝕢 = magg.RationalFunctionField(:q,magf.Rationals())

MagmaCall.MagmaValue(x::AbstractAlgebra.PolyCoeffs{Nemo.fmpq_poly}) = MagmaValue(collect(x))

MagmaCall.MagmaValue(x::fmpq) = MagmaValue(Rational{BigInt}(x))

function Base.convert(::Type{MagmaObject},x::Scalar)
    num,den = (numerator(x),denominator(x)) .|> coefficients .|> string
    magmacall("R := RationalFunctionField(Rationals()); return R!$num/R!$den")
end

function magma_matrix(x::AbstractAlgebra.Generic.MatSpaceElem,name::String)
    row,col = size(x)
    stringrat(x) = string(numerator(x))*"/"*string(denominator(x)) # without //
    stringpoly(x) = iszero(x) ? "R!0" : "R!["*join(stringrat.(coefficients(x)),",")*"]"
    stringratfun(x) = stringpoly(numerator(x)) * "/" * stringpoly(denominator(x))
    coeffs = collect(x) .|> stringratfun
    mat = "["*join(["["*join(coeffs[i,:],",")*"]" for i=1:row],",")*"]"
    "R := RationalFunctionField(Rationals()); $name := Matrix(R,$row,$col,$mat)"
end
                      
Base.convert(::Type{MagmaObject},x::AbstractAlgebra.Generic.MatSpaceElem) = magma_matrix(x,"M")*"; return M"

poly_from_magma(v) = sum(v[i]*𝕢^(i-1) for i=1:length(v); init=zero(Scalar))
ratfun_from_magma(v) = poly_from_magma(v[1]) // poly_from_magma(v[2])

function magma_nullspace(m::AbstractAlgebra.Generic.MatSpaceElem)
    s = MagmaCall.interact() do io
        MagmaCall.putcmd(io,magma_matrix(m,"M")*"; B := BasisMatrix(Nullspace(Transpose(M))); Sprint([[[Coefficients(Numerator(B[i,j])),Coefficients(Denominator(B[i,j]))] : j in [1..NumberOfColumns(B)]] : i in [1..NumberOfRows(B)]])")
        replace(MagmaCall.readtotoken(String,io,missing),"/"=>"//") |> Meta.parse |> eval
    end
    isempty(s) && return 0,nothing
    m,n = length(s),length(s[1])
    m,[ratfun_from_magma(s[i][j]) for j=1:n, i=1:m]
end

function Base.convert(::Type{Scalar},x::MagmaObject)
end
end # magma

Base.convert(::Type{Dict},p::Polynomial) = Dict{Exponent,Scalar}(e=>c for (c,e)=coefficients_and_exponents(p))

numerator_gcd(p::Polynomial) = gcd(numerator.(coefficients(p))...,numerator(zero(Scalar)),numerator(zero(Scalar)))
Base.denominator(p::Polynomial) = lcm(denominator.(coefficients(p))...,denominator(one(Scalar)),denominator(one(Scalar)))

(A::typeof(QuantumPlane.𝔸))(d::Dict{Exponent,Scalar}) = A(collect(values(d)),collect(keys(d)))
(A::typeof(QuantumPlane.𝔸))(s::Scalar) = A([s],[[0,0]])

"""Write x = q*y+r (if side==:left) or x = y*q+r (if side==:right), return (quotient=q,remainder=r).

The leading monomial of y is computed with respect to order, and is cancelled as much as possible. order takes i,j as arguments for U^iR^j."""
function Base_old_divrem(x::Polynomial, y::Polynomial, side::Symbol = :left, order = (i,j)->(i+j,i))
    side∈[:left,:right] || error("$side should be :left or :right")
    iszero(y) && throw("division by zero")

    (y_max,y_e,y_c) = (nothing,nothing,nothing)
    for (c,e)=coefficients_and_exponents(y)
        new_max = order(e...)
        if y_max==nothing || new_max>y_max
            (y_max,y_e,y_c) = (new_max,e,c)
        end
    end

    q = Dict{Exponent,Scalar}()
    r = convert(Dict,x)
    r_keys = PriorityQueue{Exponent,typeof(y_max),Base.Order.ReverseOrdering}(Base.Order.Reverse,[e=>order(e...) for (e,_)=r])
    found = Some(nothing)
    while found≠nothing
        found = nothing
        for (e,d)=r_keys
            iszero(r[e]) && continue
            (e[1]≥y_e[1] && e[2]≥y_e[2]) && (found = e; break)
        end
        found==nothing && break
        shift = found.-y_e
        s = r[found]//y_c*𝕢^(side==:left ? -shift[2]*y_e[1] : -shift[1]*y_e[2])
        # subtract s*U^shift[1]*R^shift[2]*y or y*(...) from r
        q[shift] = get(q,shift,zero(y_c)) + s
        for (d,f)=coefficients_and_exponents(y)
            g = f.+shift
            r[g] = get(r,g,zero(d)) - s*𝕢^(side==:left ? shift[2]*f[1] : f[2]*shift[1])*d
        end
        while !isempty(r_keys) && iszero(r[peek(r_keys).first])
            dequeue!(r_keys)
        end
    end
    (quotient = 𝔸(q), remainder = 𝔸(r))
end

"""Write x*s = y*q+r (if side==:left) or s*x = q*y+r (if side==:right), return (quotient=q,remainder=r,scale=s).

Both x,y,r are treated as polynomials in O∈[:U,:R], and the deg_O(r) < deg_O(y).

If O is nothing, it is chosen so as to (probably) minimize the complexity of q,r
"""
function Base.divrem(x::Polynomial, y::Polynomial, side::Symbol = :left, O = nothing)
    side∈[:left,:right] || error("$side should be :left or :right")
    iszero(y) && throw("division by zero")
    iszero(x) && return (quotient = x, remainder = x, scale = one(x))
    
    if O==:U
        O = 1
        deg_y = maximum(e[O] for e=exponents(y))
    elseif O==:R
        O = 2
        deg_y = maximum(e[O] for e=exponents(y))
    elseif O==nothing # choose O such that the top-degree term has lowest degree in the other variable
        deg_UR = deg_RU = [-1,-1]
        for e=exponents(y)
            if e[1]>deg_UR[1]
                deg_UR = [e[1],e[2]]
            elseif e[1]==deg_UR[1]
                deg_UR[2] = max(deg_UR[2],e[2])
            end
            if e[2]>deg_RU[1]
                deg_RU = [e[2],e[1]]
            elseif e[2]==deg_RU[1]
                deg_RU[2] = max(deg_RU[2],e[1])
            end
        end
        if deg_RU[2] ≥ deg_UR[2]
            O = 1
            deg_y = deg_UR[1]
        else
            O = 2
            deg_y = deg_RU[1]
        end
    else
        error("$O should be :U, :R or nothing")
    end

    deg_x = maximum(e[O] for e=exponents(x))
    deg_y_other = maximum(e[3-O] for e=exponents(y) if e[O]==deg_y)
    
    (q,r,s) = (zero(x),x,one(x))

    for d=deg_x:-1:deg_y
        # x*s == y*q + r (left); s*x == q*y + r (right)        

        deg_r_other = maximum(e[3-O] for e=exponents(r) if e[O]==d; init=-1)
        deg_r_other == -1 && continue
        
        top_y = zeros(Scalar,1+deg_y_other)
        top_r = zeros(Scalar,1+deg_r_other)

        # find (α,β) such that the degree-d part of r*β-y*α | β*r-α*y vanishes
        
        for (c,e)=coefficients_and_exponents(r)
            if e[O]==d
                top_r[1+e[3-O]] = c
            end
        end

        switch = (side,O)==(:left,1) || (side,O)==(:right,2)
        
        for (c,e)=coefficients_and_exponents(y)
            if e[O]==deg_y
                top_y[1+e[3-O]] = c*𝕢^(switch ? (d-deg_y)*e[3-O] : 0)
            end
        end

        top_y,top_r = ℚ𝕢X(top_y), ℚ𝕢X(top_r)
        γ = gcd(top_y,top_r)

        β = let p = divexact(top_y, γ) |> coefficients
            deg = length(p)-1
            𝔸([p[i]*𝕢^((side,O)==(:left,1) ? 0 : (side,O)==(:left,2) ? -d*i : (side,O)==(:right,1) ? -d*i : 0) for i=0:deg],[O==1 ? [0,i] : [i,0] for i=0:deg])
        end
        α = let p = divexact(top_r, γ) |> coefficients
            deg = length(p)-1
            𝔸([p[i]*𝕢^((side,O)==(:left,1) ? 0 : (side,O)==(:left,2) ? -deg_y*i : (side,O)==(:right,1) ? -deg_y*i : 0) for i=0:deg],[O==1 ? [d-deg_y,i] : [i,d-deg_y] for i=0:deg])
        end
        
        @debug "Step $d: " q,r,s,α,β,γ,top_y,top_r
        (q,r,s) = if side==:left
            # x*s*β == y*(q*β + α) + r*β - y*α
            (q*β + α, r*β - y*α,s*β)
        else
            # β*s*x == (β*q + α)*y + β*r - α*y
            (β*q + α, β*r - α*y,β*s)
        end
    end

    return (quotient = q, remainder = r, scale = s)
end

run_tests && @testset "Elementary polynomial operations" begin
    @test U+R == R+U
    @test 𝕢*U*R == R*U
    @test iszero(U+R+(-U-R))
    function test_divrem(x,y,side,O)
        qrs = divrem(x,y,side,O)
        if side==:left
            @test x*qrs.scale == y*qrs.quotient + qrs.remainder
        else
            @test qrs.scale*x == qrs.quotient*y + qrs.remainder
        end
        if O≠nothing
            O = O==:U ? 1 : 2
            d = maximum(e[O] for e=exponents(y))
            @test all(e->e[O]<d,exponents(qrs.remainder))
        end
    end
    for side=[:left,:right], v=[0,1,2]
        test_divrem(U^17*R^11,(U^7+v)*R^2,side,:R)
        test_divrem(U^17*R^11,U^7*(R^2+v),side,:R)
    end
end

bidegree(x) = iszero(x) ? [-1,-1] : maximum.(exponents(x))

"""Computes a common multiple m=a*x=b*y (if side==:left) or m=x*a=y*b
(if side==:right) supported on rowbasis.
Minimize the top-degree terms of a,b wrt order, which is a function taking (s,(i,j)) as arguments with s∈[:x,:y] and i,j integers representing U^iR^j.
Returns nothing if there is no solution, one solution if allsols=false, and otherwise a vector of all solutions.
"""

function ore_linalg(x,y,side::Symbol,rowbasis,order;allsols=false)
    side∈[:left,:right] || error("$side must be :left or :right")

    var = Dict(:x=>x, :y=>-y)
    
    rowbasis_reversed = Dict(p=>i for (i,p)=enumerate(rowbasis))
    maxdeg = maximum.(zip(rowbasis...))
    colbasis = [s=>[i,j] for s=[:x,:y] for i=0:maxdeg[1] for j=0:maxdeg[2] if all(e->haskey(rowbasis_reversed,e.+(i,j)),exponents(var[s]))]
    sort!(colbasis,lt=(p,q)->order(p...)<order(q...))

    M = matrix_space(ℚ𝕢,length(rowbasis),length(colbasis))()
    for (col,(s,(i,j)))=enumerate(colbasis)
        for (c,e)=coefficients_and_exponents(var[s])
            M[rowbasis_reversed[e.+(i,j)],col] += c*𝕢^(side==:left ? j*e[1] : e[2]*i)
        end
    end
#    (nullity,N) = magma_nullspace(M)
    (nullity,N) = nullspace(M)
    nullity==0 && return nothing

    sols = NTuple{2,Polynomial}[]
    # we now rely on the fact that the nullspace is computed by rref,
    # so the first column has the lowest-index nonzeros.
    for col=1:nullity
        sol = Dict(s=>Dict{Exponent,Scalar}() for s=[:x,:y])
        for (row,(s,p))=enumerate(colbasis)
            if !iszero(N[row,col])
                sol[s][p] = N[row,col]
            end
        end
        push!(sols,(𝔸(sol[:x]),𝔸(sol[:y])))
        allsols || return sols[1]
    end
    return sols
end

"""Computes the common multiples of x,y on side∈[:left,:right]
of smallest degree⋅direction
"""
function ore_linalg(x,y,side::Symbol=:left,direction=nothing)
    iszero(x) && return (one(x),zero(x))
    iszero(y) && return (zero(x),one(x))

    if direction==nothing
        direction = (1,1)
    end

    d = 0
    while true
        if direction[1]==0
            basis = [[i,j] for i=0:d for j=0:d^2]            
        elseif direction[2]==0
            basis = [[i,j] for i=0:d^2 for j=0:d]
        else
            basis = [[i,j] for i=0:d for j=0:d if i*direction[1]+j*direction[2]≤d]
        end
        sol = ore_linalg(x,y,side,basis,(s,e)->e[1]*direction[1]+e[2]*direction[2])
        if sol≠nothing # try to trim solution
            while true
                lastsol = sol
                pop!(basis)
                sol = ore_linalg(x,y,side,basis,(s,e)->e[1]*direction[1]+e[2]*direction[2])
                sol==nothing && return lastsol
            end
        end
        d += 1
    end
end

Oscar.degree(p::Polynomial,O) = maximum(e[O==:U ? 1 : 2] for e=exponents(p))
otherside(side::Symbol) = side==:left ? :right : :left

"""Computes the common multiples of x,y on side∈[:left,:right] of smallest degree in variable O∈[:U,:R]
"""
function ore_syzygy(x,y,side::Symbol = :left,O = nothing)
    a = [one(x) zero(x); zero(x) one(x)]
    while !iszero(y)
        @info "ore_syzygy" x,y
        (quotient, remainder, scale) = divrem(x,y,otherside(side),O)
        if iszero(quotient) # we're not making progress with free O
            O = :U
        end
        (x,y) = (y,remainder)
        a = if side==:left
            [zero(x) one(x); scale -quotient]*a
        else
            a*[zero(x) scale; one(x) -quotient]
        end
    end
    (side==:left ? a[2,1] : a[1,2],-a[2,2])
end

run_tests && @testset "Ore operation with linear algebra" begin
    @test ore_linalg(U,R) ∈ [(𝕢^-1*R,U),(R,𝕢*U)]
    @test ore_linalg(U,R,:right) ∈ [(R,1//𝕢*U),(𝕢*R,U)]
    @test ore_linalg(U+R,U+R) == (one(U),one(U))
    (a,b) = ore_linalg(U^2+R,R^2+U,:left)
    @test a*(U^2+R) == b*(R^2+U)
    (a,b) = ore_linalg(U^2+R,R^2+U,:right)
    @test (U^2+R)*a == (R^2+U)*b
end

run_tests && @testset "Ore operation with syzygy" begin
    function test_ore(x,y,side,O)
        (u,v) = ore_syzygy(x,y,side,O)
        if side==:left
            @test u*x == v*y
        else
            @test x*u == y*v
        end
    end
    for side=[:left,:right], O=[:R,:U,nothing]
        test_ore(U,R,side,O)
        test_ore(U+R,U+R,side,O)
        test_ore(U^2+R,R^2+U,side,O)
    end
end

ore(x,y,side::Symbol=:left,O=nothing) = ore_syzygy(x,y,side,O)

################################################################
# now quotient types, left and right
"""A fraction over Polynomial. S is :left or :right"""
struct Fraction{S}
    den::Polynomial
    num::Polynomial
end

Fraction{S}(p::Polynomial) where S = Fraction{S}(one(p),p)
Fraction(p::Polynomial) = Fraction{:left}(p)
Fraction(p::Polynomial,q::Polynomial) = Fraction{:left}(p,q)
Base.inv(p::Polynomial) = Fraction{:left}(p,one(p))

Base.:/(p::Polynomial,q::Polynomial) = Fraction{:right}(q,p)
Base.:\(p::Polynomial,q::Polynomial) = Fraction{:left}(p,q)

Base.promote_rule(::Type{Fraction{:right}},::Type{Fraction{:left}}) = Fraction{:right}

Base.:+(x::Fraction, y) = +(promote(x,y)...)
Base.:-(x::Fraction, y) = -(promote(x,y)...)
Base.:*(x::Fraction, y) = *(promote(x,y)...)
Base.:+(x, y::Fraction) = +(promote(x,y)...)
Base.:-(x, y::Fraction) = -(promote(x,y)...)
Base.:*(x, y::Fraction) = *(promote(x,y)...)

function Base.show(io::IO, f::Fraction{S}) where S
    (d,n) = string.((f.den,f.num))
    if match(r" [+-] ",d)≠nothing d = "("*d*")" end
    if match(r" [+-] ",n)≠nothing n = "("*n*")" end
    if S==:left
        print(io, d, " \\ ",n)
    else
        print(io, n, " / ",d)
    end
end

for (side,oside)=[(:(:left),:(:right)),(:(:right),:(:left))]
    @eval Base.promote_rule(::Type{Fraction{$side}},::Type{Polynomial}) = Fraction{$side}
    @eval Base.promote_rule(::Type{Fraction{$side}},::Type{Scalar}) = Fraction{$side}
    @eval Base.promote_rule(::Type{Fraction{$side}},::Type{Int}) = Fraction{$side}
    @eval Base.promote_rule(::Type{Fraction{$side}},::Type{Rational}) = Fraction{$side}
    
    @eval Base.convert(::Type{Fraction{$side}}, x::Polynomial) = Fraction{$side}(x)
    @eval Base.convert(::Type{Fraction{$side}}, x::Scalar) = Fraction{$side}(𝔸(x))

    @eval Base.convert(::Type{Fraction{$side}}, x::Int) = Fraction{$side}(𝔸(x))

    @eval Base.convert(::Type{Fraction{$side}}, x::Rational) = Fraction{$side}(𝔸(x))
    
    @eval function Base.convert(::Type{Fraction{$side}}, f::Fraction{$oside})
        (a,b) = ore(f.den,f.num,$side)
        Fraction{$side}(b,a)
    end

    @eval function Base.inv(f::Fraction{$side})
        Fraction{$side}(f.num,f.den)
    end

    @eval Base.iszero(f::Fraction{$side}) = iszero(f.num)

    @eval Base.isone(f::Fraction{$side}) = f.num == f.den

    @eval Base.zero(f::Fraction{$side}) = Fraction{$side}(zero(f.num))

    @eval Base.one(f::Fraction{$side}) = Fraction{$side}(one(f.num))
    
    @eval Base.numerator(f::Fraction{$side}) = f.num
    @eval Base.denominator(f::Fraction{$side}) = f.den
    
    @eval Base.:(==)(f::Fraction{$side},g::Fraction{$side}) = convert(Fraction{$oside},f) == g

    @eval Base.:-(f::Fraction{$side}) = Fraction{$side}(f.den,-f.num)

    @eval Base.:-(f::Fraction{$side}, g::Fraction{$side}) = f+(-g)

    @eval Base.:/(f::Fraction{$side}, g::Fraction{$side}) = f*inv(g)

    @eval Base.:\(f::Fraction{$side}, g::Fraction{$side}) = inv(f)*g

    @eval Base.:^(f::Fraction{$side}, g::Fraction{$side}) = inv(g)*f*g

    @eval function Base.:^(f::Fraction{$side}, i::Int)
        if i<0
            inv(f)^(-i)
        elseif i==0
            one(f)
        elseif i==1
            f
        elseif iseven(i)
            (f*f)^(i÷2)
        else
            (f*f)^(i÷2)*f
        end
    end

    @eval Base.hash(f::Fraction{$side}) = hash(f.den,hash(f.num))

    @eval function simplify_scalars(f::Fraction{$side})
        l = lcm(denominator(f.den),denominator(f.num))//gcd(numerator_gcd(f.den),numerator_gcd(f.num)) |> Scalar
        l.parent = ℚ𝕢
        Fraction{$side}(f.den*l,f.num*l)
    end

    @eval function simplify(f::Fraction{$side})
        p = convert(Fraction{$side},convert(Fraction{$oside},f))
        simplify_scalars(p)
    end
end

Base.:(==)(f::Fraction{:left},g::Fraction{:right}) = g == f
Base.:(==)(f::Fraction{:right},g::Fraction{:left}) = g.den*f.num == g.num*f.den

Base.:(==)(f::Fraction{:left},g::Polynomial) = f.den*g == f.num
Base.:(==)(f::Fraction{:right},g::Polynomial) = g*f.den == f.num
Base.:(==)(f::Polynomial,g::Fraction) = g == f

Base.:/(f::Fraction{:right},g::Polynomial) = Fraction{:right}(f.den*g,f.num)
Base.:/(f::Polynomial,g::Fraction{:right}) = Fraction{:right}(g.num,f*g.den)
Base.:\(f::Polynomial,g::Fraction{:left}) = Fraction{:left}(f*g.den,g.num)
Base.:\(f::Fraction{:left},g::Polynomial) = Fraction{:left}(f.num,f.den*g)

Base.:*(f::Fraction{:left},g::Polynomial) = Fraction{:left}(f.den,f.num*g)
Base.:*(f::Polynomial,g::Fraction{:right}) = Fraction{:right}(g.den,f*g.num)

function Base.:+(f::Fraction{:left}, g::Fraction{:left})
    (a,b) = ore(f.den,g.den,:left)
    Fraction{:left}(a*f.den,a*f.num+b*g.num)
end

function Base.:+(f::Fraction{:right}, g::Fraction{:right})
    (a,b) = ore(f.den,g.den,:right)
    Fraction{:right}(f.den*a,f.num*a+g.num*b)
end

function Base.:*(f::Fraction{:left}, g::Fraction{:left})
    (a,b) = ore(f.num,g.den,:left)
    Fraction{:left}(a*f.den,b*g.num)
end

function Base.:*(f::Fraction{:right}, g::Fraction{:right})
    (a,b) = ore(f.den,g.num,:right)
    Fraction{:right}(g.den*b,f.num*a)
end

"""Computes the series expansion f = ∑_{i,j} fᵢⱼUⁱRʲ + O(Uᵐ,Rⁿ)
"""
function series(f::Fraction{side}, m::Int = 10, n::Int = m) where side
    s = Matrix{Scalar}(undef,m,n)
    den, num = convert(Dict,f.den), convert(Dict,f.num)
    c₀ = get(den,[0,0],zero(𝕢))
    iszero(c₀) && error("Denominator is not of the form 1+…")
    
    # solve f.num = f.den*s (if side==:left) or s*f.den (if side==:right),
    # degree by degree
    for i=0:m-1, j=0:n-1
        v = get(num,[i,j],zero(𝕢))
        for ((α,β),c) = den
            if (α,β)≠(0,0) && α≤i && β≤j
                v -= c*s[i+1-α,j+1-β]*𝕢^(side == :left ? β*(i-α) : (j-β)*α)
            end
        end
        s[i+1,j+1] = v//c₀
    end
    s
end

run_tests && @testset "Fractions" begin
    @test inv(inv(R)) == R
    (lR,lU) = Fraction{:left}.((R,U))
    (rR,rU) = Fraction{:right}.((R,U))
    @test lR == rR == R
    @test lU == rU == U
    @test lR*lU == 𝕢*lU*lR == rR*rU == 𝕢*rU*rR
    for u=[lU,rU,U], r=[lR,rR,R]
        @test u/r == U/R
        @test u\r == U\R
    end
    @test inv(R)+inv(U) == (𝕢*U*R) \ (𝕢*U + R)
end

end
