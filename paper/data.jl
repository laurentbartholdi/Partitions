# The automata of the paper, in two notations:
#  * Automaton{N}(arcs) (src/automata.jl): states 1..N and an implicit initial R into state 1;
#    an arc (i, j, 1) reads R, (i, j, 2) reads U, and (i, i, 3) accepts by a final U;
#  * strings for QuantumWZ.automaton and compile: "0R1 1U1 1U∞ …", with 0 initial and ∞ final;
#    parallel arcs add their weights, so weighted and nondeterministic automata are allowed.
# spec(t) converts the first notation into the second.

@isdefined(PAPER_COMMON) || include("common.jl")

# §1: odd parts R(U+RR)*U and distinct parts R(R+UR)*U.
const L_odd = Partitions.euler1
const L_distinct = Partitions.euler2

# §4.1: no part divisible by λ (states: the height modulo λ), and no part occurring λ or more
# times (states: one more than the number of letters U read at the current height).
glaisher_nodiv(λ) = Automaton{λ}([[(i, mod1(i + 1, λ), 1) for i in 1:λ]; [(i, i, 2) for i in 1:λ-1]; [(i, i, 3) for i in 1:λ-1]])
glaisher_mult(λ) = Automaton{λ}([[(k, 1, 1) for k in 1:λ]; [(k, k + 1, 2) for k in 1:λ-1]; [(k, k, 3) for k in 1:λ-1]])

"Arcs (source, letter, target) between named states, with s initial and ∞ final, as a string for compile."
function namedspec(arcs)
    names = sort(unique([x for (a, _, b) in arcs for x in (a, b) if x ∉ ("s", "∞")]))
    num = Dict(x => string(k) for (k, x) in enumerate(names))
    num["s"], num["∞"] = "0", "∞"
    join(("$(num[a])$v$(num[b])" for (a, v, b) in arcs), " ")
end

# §4.2, Figure 1: Primc's admissible partitions with boundary (2,0,0). State names are those of the
# TikZ source of the figure: O20 … O02 are the circles τβ (the preceding even pair), B10, B00a, B00b,
# B01 the circles 10¹, 00¹, 00², 01¹; E… are the ten plain rectangles 00; Dt…, Db…, Dtt19, Dtb15,
# Dbb23 are the rectangles 10, 01, 20, 11, 02. The tags U_m, U_t, U_b of the figure are dropped.
const primc_admissible_arcs = let
    U(pairs) = [(a, "U", b) for (a, b) in pairs]
    Rr(pairs) = [(a, "R", b) for (a, b) in pairs]
    arcs = [Rr([("s", "O02")]);
            U([("O00", "B00a"), ("B00a", "B00b"), ("O10", "B10"), ("O01", "B01")]);
            Rr([("O20", "E20"), ("O10", "E10"), ("B10", "E10b"), ("B00b", "E00c"), ("B00a", "E00b"),
                ("O00", "E00"), ("O11", "E11"), ("O01", "E01"), ("B01", "E01b"), ("O02", "E02")]);
            U([("E20", "Dt22"), ("E10", "Dt8"), ("E10", "Db6"), ("E10b", "Dt11"), ("E00b", "Dt11"),
               ("E00b", "Db6"), ("E00", "Dt8"), ("E00", "Db4"), ("E11", "Dt21"), ("E11", "Db6"),
               ("E01", "Dt21"), ("E01", "Db4"), ("E01b", "Db6"), ("E02", "Db4"), ("Dt22", "Dtt19"),
               ("Dt8", "Dtt19"), ("Dt8", "Dtb15"), ("Dt21", "Dtb15"), ("Db4", "Dbb23")]);
            Rr([("Dt22", "O10"), ("Dtt19", "O20"), ("Dt8", "O10"), ("Dt11", "O10"), ("Dtb15", "O11"),
                ("Db6", "O01"), ("Dt21", "O10"), ("Db4", "O01"), ("Dbb23", "O02")]);
            Rr([(e, "O00") for e in ["E20", "E10", "E10b", "E00c", "E00b", "E00", "E11", "E01", "E01b", "E02"]])]
    accepting = ["B10", "B00b", "B00a", "B01", "Dt22", "Dt8", "Dt11", "Db6", "Dt21", "Db4", "Dtt19", "Dtb15", "Dbb23"]
    # a word is accepted when it ends in an accepting state; its last letter is U
    [arcs; [(a, "U", "∞") for (a, v, b) in arcs if v == "U" && b in accepting]]
end
const primc_admissible = namedspec(primc_admissible_arcs)

# §4.2, Figure 1: parts with residues 2,3,4,4,5,6 modulo 8; r0 … r7 record the height modulo 8, and
# r4p (4′ in the figure) the second colour of the residue 4.
const primc_residues = namedspec([[("s", "R", "r1")];
                                  [("r$j", "R", "r$(mod(j + 1, 8))") for j in 0:7];
                                  [("r$j", "U", "r$j") for j in 2:6];
                                  [("r4", "U", "r4p"), ("r4p", "U", "r4p"), ("r4p", "R", "r5")];
                                  [("r$j", "U", "∞") for j in [2, 3, 4, 4, 5, 6]];
                                  [("r4p", "U", "∞")]])

# §4.3, Figure 2: gaps at least 2 and least part at least i (states numbered as in the figure),
# and parts ≡ ±i modulo 5 (state k records the height k modulo 5).
rr_gap(i) = "0R$(i == 1 ? 1 : 3) 1R1 1U2 1U∞ 2R3 3R1"
rr_residue(i) = "0R1 1R2 2R3 3R4 4R5 5R1 " * join(("$(r)U$r $(r)U∞" for r in (i == 1 ? (1, 4) : (2, 3))), " ")

# §4.6, Figure 3: the two five-state automata (states numbered as in the figure), and the automaton
# of the conjugate partitions of L_B (words reversed, R and U interchanged), read by the c-equations
# of (54): its initial interior states are 2 and 4, and its final interior state is 1.
const L_A = Automaton{5}([(1,2,1), (2,3,2), (2,2,3), (3,1,2), (3,4,1), (3,3,3), (4,3,2), (4,5,1), (4,4,3), (5,4,2), (5,5,3)])
const L_B = Automaton{5}([(1,2,1), (2,1,2), (2,3,1), (2,2,3), (3,2,2), (3,4,1), (4,5,2), (4,4,3), (5,3,1)])
const L_B_conjugate = "0R2 0R4 1U∞ 2U1 1R2 3U2 2R3 4U3 5R4 3U5"

const PAPER_DATA = true
