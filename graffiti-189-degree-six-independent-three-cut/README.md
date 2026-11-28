# Graffiti.pc #189, d=6: independent three-cuts and universal ports

For a finite connected simple graph in the degree-six Graffiti
hypotheses, assume the graph remains connected after deleting any
fewer than three vertices. Then deleting an independent set of
three vertices leaves at most two components. Thus an independent
three-vertex separator leaves exactly two. There is no spanning-path
claim in this package.

Independently of the edges inside the cut, if three components
remain, some outside vertex sees all three terminals. In the
absence of such a port, a terminal with a high port in each shore
forces all three shores to have precisely three of its ports and
two of its distance-two vertices, hence to have size five. At
least two terminals must have this property: otherwise the single
exceptional low port would either see every terminal or would
prevent the sole good terminal from paying its degree budget.
The two good terminals force the third terminal to have at least
four ports in every all-high shore; its foreign port cap prevents
that on two shores, yielding the contradiction.

For an independent three-cut, the earlier isolated-terminal charge
forces every terminal to use the unique low vertex as its sole
port in the same shore. That shore must be a singleton. Its six
distance-two slots then contain exactly three visible vertices on
each of the other two shores. Each such shore has at least four
dark vertices, and the singleton's parity cap makes all dark
vertices have a visible neighbor. For an isolated terminal,
exact local budgets give two ports in each side, both universal
to the terminals. If every terminal is isolated within the cut,
every visible vertex is accordingly universal, contradicting two
rather than three ports per terminal.

The top-level graph statements are
`independent_three_cut_at_most_two_components` and
`universal_port_of_three_components` in namespace
`Graffiti189LongestPath.ThresholdSix.ThreeCut`.

## Replay

Use Lean/Mathlib v4.19.0 with the strict
[three-cut count package](../graffiti-189-degree-six-three-cut-count/)
on LEAN_PATH, including its published object prerequisites.
Compile the following from `src`, in order, with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`:

1. `SixTripleCutTerminalRank189.lean`
2. `SixTripleCutUniversalPort189.lean`
3. `SixTripleCutSingleton189.lean`
4. `SixTripleCutSingletonIsolate189.lean`
5. `SixIndependentTripleCut189.lean`

`StrictReplay.log` records only standard axioms. There is no
enumeration or solver trace in this proof.
