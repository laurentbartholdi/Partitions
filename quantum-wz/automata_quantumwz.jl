# Certify all differences between automata with the same growth series.
#
# Input: one line per family, in the format
#     Automaton[[0R1 1R2 1U1 1U∞ 2R1], [...], ...]
# A transition iVj goes from state i to state j reading V ∈ {R, U}; 0 is the initial
# and ∞ the final state. R = Y and U = X in the quantum plane YX = tXY, so an
# automaton stands for the sum of its accepted words, and the growth series is S of
# that sum: Σ_w t^(number of pairs R…U in w). Every accepted word must have the form
# R…U (initial transitions read R, final transitions read U); then the realization is
# normalized as in `automaton` (Y m X = t X σ(m) Y, weight t per inner letter).
#
# A list is certified when its proved differences connect all its automata (S is
# additive); the script also reports that.
#
# Output: one line per difference: status, method (rational, zero_marginal, channels,
# or channels+remainder when a block's partial sums are channels only up to a
# remainder that tends to 0), the readings, the time, and for channel proofs the
# period, the dilation witnesses (Γ shown by its z-degree when long) and the pole
# order of each block's remainder fit (:none for an exact decomposition).
#
# Usage:  julia automata_quantumwz.jl FILE [FIRST LAST [MODE [TIME]]]   (line range, 1-based)
# MODE = all (default): every difference within each list; MODE = spanning: the
# differences 1−j first, then others only as needed to connect each list.
# TIME: the time limit of the channel search per difference, in seconds (300).
using Oscar
include(joinpath(@__DIR__, "QuantumWZ.jl"))
using .QuantumWZ

ctx = setup()

lines = filter(!isempty, strip.(readlines(ARGS[1])))
first_line, last_line = length(ARGS) >= 3 ? parse.(Int, ARGS[2:3]) : (1, length(lines))
mode = length(ARGS) >= 4 ? ARGS[4] : "all"
limit = length(ARGS) >= 5 ? parse(Float64, ARGS[5]) : 300.0
counts = Dict{Any, Int}()
connected = 0                     # lines whose proved differences connect all automata
total = time()

"Run one difference, print a line, and return true if it is proved."
function run_pair(k, auts, i, j)
  t0 = time()
  r = try
    attempt(ctx, compile(ctx, difference(auts[i], auts[j])...)...; time_limit = limit)
  catch err
    (; status = :error, method = sprint(showerror, err)[1:min(end, 120)])
  end
  method = get(r, :method, get(r, :reason, nothing))
  haskey(r, :remainders) && (method = Symbol(method, "+remainder"))
  key = (r.status, method)
  counts[key] = get(counts, key, 0) + 1
  short(x) = (s = string(x); length(s) <= 40 ? s : "(z-degree $(QuantumWZ.zdeg(x)))")
  how = r.status == :proved && r.method == :channels ?
        "period $(r.period); " * join(["λ=$(p.λ) μ=$(p.μ) χ=$(p.χ)" * (isone(p.Γ) ? "" : " Γ=$(short(p.Γ))")
                                       for p in r.parts if p.kind == :dilation], "; ") *
        (haskey(r, :remainders) ? "; remainder poles $(r.remainders)" : "") : ""
  println(rpad("$k:$i−$j", 10), rpad(string(r.status), 9), rpad(string(something(method, "")), 19),
          rpad(string(get(r, :reading, "")), 22), rpad("$(round(time() - t0; digits = 1))s", 8), how)
  flush(stdout)
  return r.status == :proved
end

for k in first_line:last_line
  auts = [automaton(ctx, a) for a in automata(lines[k])]
  n = length(auts)
  up = collect(1:n)               # union-find: S is additive, so proved differences compose
  root(i) = up[i] == i ? i : (up[i] = root(up[i]))
  join!(i, j) = (up[root(i)] = root(j))
  if mode == "all"
    for i in 1:n, j in i+1:n
      run_pair(k, auts, i, j) && join!(i, j)
    end
  else
    for j in 2:n
      run_pair(k, auts, 1, j) && join!(1, j)
    end
    for j in 2:n, i in 2:n
      (i == j || root(j) == root(1) || root(i) != root(1)) && continue
      run_pair(k, auts, min(i, j), max(i, j)) && join!(i, j)
    end
  end
  all_joined = length(unique(root.(1:n))) == 1
  global connected += all_joined
  all_joined || println("$k: not all differences certified")
end
println("lines $(first_line)–$(last_line): ", sort(collect(counts); by = string), "; lines with all differences ",
        "certified (directly or as sums of proved ones): $connected of $(last_line - first_line + 1)   ",
        round(time() - total; digits = 1), "s")
