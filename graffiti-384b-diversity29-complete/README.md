# Graffiti.pc #384b at 29 distinct triangle counts

**Every finite simple graph on n vertices with exactly 29 distinct vertex triangle counts has a two-dominating set of size at most n − 15.** Each vertex outside the set has at least two distinct neighbors in it. A vertex's count is the number of unordered triangles incident to it, and zero contributes a distinct value whenever it occurs. The sole numerical hypothesis is the number of distinct counts. The result includes disconnected graphs and arbitrary orders. [Lean theorem and existence statement](DiversityTwentyNineComplete.lean) · [Definitions](prior/Proof384b.lean)

Ermelinda DeLaViña's January 2010 catalogue entry asks whether every connected graph on n > 2 vertices satisfies γ₂(G) ≤ floor(n − |T|/2), for the set T of vertex triangle counts. At |T|=29 this is exactly n − 15. The general conjecture remains open. [Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue dataset, entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## Exhaustion of the nonleaf counts

Let q count the vertices of degree at least two. The following previously verified results were checked against published revision `01802cf967aa8af51efce7423e29f09302e64b41`.

| Nonleaf count | Coverage at 29 triangle counts |
| --- | --- |
| q ≤ 27 | Impossible. At least 28 distinct positive triangle counts occur, each requiring a different nonleaf. The published quota reduction also proves this lower bound under a hypothetical failure. [Quota reduction](https://github.com/vjdad4m/maths/blob/01802cf967aa8af51efce7423e29f09302e64b41/graffiti-384b-diversity29/FrontierTwentyNine384b.lean) |
| q = 28 | The minimum nonleaf case is covered by `TwentyEight.original_bound`. [28-nonleaf theorem](https://github.com/vjdad4m/maths/blob/01802cf967aa8af51efce7423e29f09302e64b41/graffiti-384b-28-nonleaf-complete/FinishNonleaves28.lean) |
| q = 29 | The private-triangle argument and the earlier high-vertex reductions give `PrivatePatch.twenty_nine_nonleaves`. [29-nonleaf theorem](https://github.com/vjdad4m/maths/blob/01802cf967aa8af51efce7423e29f09302e64b41/graffiti-384b-29-nonleaf-profile/CompleteFourRoots.lean) |
| q = 30 | The three-ear theorem is `EarMix.original_bound`. [30-nonleaf theorem](https://github.com/vjdad4m/maths/blob/01802cf967aa8af51efce7423e29f09302e64b41/graffiti-384b-30-nonleaf-complete/OriginalSix30.lean) |
| q ≥ 31 | The many-nonleaves case is covered by `Quota29.Finish.many_nonleaves`. [Many-nonleaves theorem](https://github.com/vjdad4m/maths/blob/01802cf967aa8af51efce7423e29f09302e64b41/graffiti-384b-diversity29/QuotaFinish29.lean) |

The published `EarMix.remaining_nonleaves` already combines the quota restriction with the 28- and 30-nonleaf theorems. A strict failure would therefore have q=29. Applying the 29-nonleaf theorem rules it out. The new source records this implication for every finite simple graph, evaluates the numerical bound, and extracts an actual finite set witnessing at least fifteen omissions. The structural and sampling arguments retain their attribution to the earlier packages. [Full-band proof](DiversityTwentyNineComplete.lean)

## Replay

The source archive contains the new module and the full project import closure. The two incorporated releases agree on both source and compiled-object hashes for all 320 modules they share. The recorded replay compiled the new source with warnings as errors and used 419 hash-verified predecessor objects. It audited the printed axioms of all three theorems. [Transcript](StrictBand29.log) · [Predecessor source hashes](PREDECESSORS.sha256) · [Replay script](replay.py)

From the extracted directory, run the following in the shared workspace.

```sh
w=/absolute/path/to/predecessor-checkout
BAND_LEAN_BIN="$w/graff384b-codex/.deps/lean-4.19.0-linux/bin" \
BAND_MATHLIB="$w/graff384b-codex/.deps/mathlib4" \
python3 -B replay.py --checked "$w"
```

For a full source rebuild on another machine, set those variables to Lean 4.19.0 (commit `6caaee842e94`) and Mathlib 4.19.0 (commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`) with compiled Mathlib dependencies, and use `python3 -B replay.py --cold`. The recorded audit used the checked predecessor mode.

The frozen 29-nonleaf source archive has SHA-256 `800c85db53a3ed0e2dbe7ce3dd674286b1736ce5b279ddac41107f67a28a43e7`. The 30-nonleaf release archive has SHA-256 `2a57262734b4c1912f8f3c4c521f71cf79795437dd17920d36c2d1cc507ccebf`.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
