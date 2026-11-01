# Partitions

Julia code accompanying L. Bartholdi, *Automatic partition identities*: partition languages
given by finite automata, their series in the quantum plane, and holonomic certificates of
identities between them. The scripts in [`paper/`](paper) reproduce the computations of the
paper, section by section.

## Installation

Julia ≥ 1.11 is required. The dependency OpenFST.jl is not registered; `Project.toml` points to
its repository, and `Pkg.instantiate()` builds it (this needs a C++ compiler and CMake).

```sh
git clone https://github.com/laurentbartholdi/Partitions.git
cd Partitions
julia --project=. -e 'using Pkg; Pkg.instantiate()'
make -C exhaustivautomata        # the enumerator, needed only by allautomata
```

## Notation

| paper | `Partitions` (module `QuantumPlane`) | `QuantumWZ` (fields of `Partitions.qwzctx`) |
|---|---|---|
| q | `𝕢` | `t` |
| quantum plane 𝔸, generators U, R | `𝔸`, `U`, `R` | `A`, `X`, `Y` |
| operator algebra 𝒪, generators R, Υ | | `O`, `Yo`, `T` |

Automata are given in one of two forms.

* `Automaton{N}(arcs)`: states `1:N`, and an implicit initial letter R into state 1. An arc
  `(i, j, 1)` reads R, `(i, j, 2)` reads U, and `(i, i, 3)` makes `i` accepting by a final U.
  Such an automaton is deterministic, and its language is a set of boundary words `R…U`.
* A string such as `"0R1 1R2 1U1 1U∞ 2R1"` (`QuantumWZ.automaton`, `spec`): an arc `iVj` reads
  `V`, `0` is the initial and `∞` the final state. Parallel arcs add their weights, so these
  strings also describe weighted and nondeterministic automata (Figure 1 of the paper).

## From the paper to the code

| paper | code |
|---|---|
| area series ε(H) of an automaton (§1) | `growthseries(t, n)` (counts the empty partition), `pathseries(s, n)` |
| path series H as a fraction in 𝔸 (§1, §3.1) | `quantumseries(t)` |
| normalized marginal system (L, f, d), eqs. (8)–(9) | `Partitions.compile(t)`, `Partitions.compile(s)` |
| difference of two series, block-diagonal system (§3.5) | `Partitions.difference(p₁, p₂)` |
| coefficients b_n of the formal boundary b, eq. (11) | `Partitions.bvalues(p, n)` |
| disproof by ν(b_n) < n + 1 (Theorem A(3), Lemma 3.5) | `Partitions.rate_ok(p, n)` |
| certificate searches (§3.8, Appendix A) | `Partitions.attempt(p)` |
| exhaustive enumeration (§3.8, §4.6) | `allautomata(n; area)`, `cluster`, `quantum-wz/automata_quantumwz.jl` |

`attempt` returns a named tuple whose `status` is `:nonzero` (some ν(b_n) < n + 1, so the identity
fails), `:proved` with a `method` (`:zero_marginal`: the marginal vanishes, decided from the
exceptional indices of Lemma 3.4; `:rational`, `:polynomial`: operator witnesses of Appendix A;
`:channels`: the b_n along progressions are sums of first-order series, cancelled by dilation
witnesses as in Proposition 3.7), or `:unknown`, which is not a disproof.

```julia
using Partitions
odd = Automaton{2}([(1,1,2), (1,2,1), (2,1,1), (1,1,3)])     # R(U+RR)*U, §1
distinct = Automaton{2}([(1,1,1), (1,2,2), (2,1,1), (1,1,3)])  # R(R+UR)*U
growthseries(odd, 30) == growthseries(distinct, 30)           # Euler's identity to q^30
quantumseries(odd)                                            # H_o in 𝔸
p = Partitions.difference(Partitions.compile(odd), Partitions.compile(distinct))
Partitions.bvalues(p, 6)                                      # b_0, …, b_6 ∈ ℚ(q)
Partitions.attempt(p)                                         # status = :proved
```

## Reproducing the paper

```sh
julia --project=. paper/runall.jl      # §1 and §4; also run by `]test Partitions`
julia --project=. paper/primc.jl       # a single section
julia --project=. paper/enumeration.jl # §3.8, §4.6; PARTITIONS_N=5 for the search of §4.6
```

Identities between polynomials, rational functions and operators are checked exactly, as are
the dimensions of the linear systems of the searches. Statements about series (equal counts,
coefficients b_n, solutions of systems) are checked to the order given in each script. The
engine works over ℚ(q), so in §4.4 and §4.5 the statistic variables are specialized to integers
for the checks on the automata; the identities in these variables are checked symbolically.

| § | script | checks |
|---|---|---|
| 1, Cor. 4.2 | `euler.jl` | series of L_o, L_d; the systems (8)–(9) and the operators of §1; b_n as bounded counts and ν(b_n) ≥ n + 1; the states m_{o,1}, m_{d,1}, eq. (2), u − v = q²Υψ, b = qΥb′; `attempt` |
| 4.1 | `glaisher.jl` | series for λ = 2, …, 6; the dilation witness (16); b_{λk} = [R^{λk}](u_α − u_β) (Cor. 3.8) |
| 4.2 | `primc.jl` | the automata of Figure 1 (29 and 9 interior states); the transfer system (18) and the four products of Theorem B; the quadratic invariant (19) and its 60 × 20 search; the factorization (20); the certificates (25)–(26) and their 4 × 3 and 5 × 4 searches; (24) solves (21); (27)–(28) and (22)–(23) at z = 1; the difference system of size 38 |
| 4.3 | `rogers_ramanujan.jl` | the automata of Figure 2 against the sums and products (31); the data L_gap, L_Σ, f_i, d_i; (32)–(34), (36), (37) for small indices; (35) and its 5 × 4 search |
| 4.4 | `bessenrodt.jl` | (38); (40); the system L, f, d: the values m(0), and b_n as bounded counts |
| 4.5 | `berkovich_uncu.jl` | (41); the automata (42): b_n as bounded counts; (44) = (45) = direct count; (46), (47); (50) with (51) for L = 2, 3, 4 |
| 4.6 | `five_states.jl` | the automata of Figure 3 and the conjugate automaton; the kernels (54); (56)–(60) in 𝒪; ψ ∈ ℤ[q][[R]], (58), c₃ = q(1 + R) + Nψ and b = qΥφ coefficientwise; `attempt` |
| 3.8, 4.6 | `enumeration.jl` | all automata with at most 4 (or 5) states, their families of equal series, written for the batch driver |

The automata of the paper are in [`paper/data.jl`](paper/data.jl), with state names following the
figures.

## Exhaustive searches

`exhaustivautomata/dfa n --partial` lists one minimal deterministic interior automaton for each
language recognized with at most `n` states (222354 for `n = 4`, 14614080 for `n = 5`).
`allautomata` reads them, `cluster` groups them by series, and
`quantum-wz/automata_quantumwz.jl FILE` certifies the differences within each family:

```julia
using Partitions
families = filter(c -> length(c.first) > 1, cluster(allautomata(4; area = 30)))
open(io -> foreach(c -> println(io, c.first), families), "families4.txt", "w")
```
```sh
julia --project=. quantum-wz/automata_quantumwz.jl families4.txt
```

## Layout

* `src/`: automata and their enumeration (`automata.jl`), the quantum plane and its fractions
  (`qplane.jl`), marginal systems and certificates (`qwz.jl`), series and conversions (`tools.jl`);
* `quantum-wz/`: the certificate engine `QuantumWZ` and its batch driver;
* `exhaustivautomata/`: the C++ enumerator of automata;
* `paper/`: the scripts reproducing the paper; `test/runtests.jl` runs them.
