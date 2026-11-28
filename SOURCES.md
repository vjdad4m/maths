# Conjecture sources

The [problem index](README.md) records results in this repository. The links below identify the original statements and their numbering. The numbering systems are separate.

| Collection | Where to find the problems | How to interpret the index |
| --- | --- | --- |
| AutoGraphForge | [Pinned normalized survivor list](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt) | “AutoGraphForge line N” means physical line N in this exact file, not a conjecture number in another collection. |
| Graffiti³ | [Randy Davila’s Graffiti³ paper, Research Square v1](https://assets-eu.researchsquare.com/files/rs-8493329/v1_covered_f3b2ebd5-1eff-4ba6-aa7a-671608894aaf.pdf) | “Graffiti³ #N” means the numbered conjecture in this paper, including lettered parts where applicable. |
| Graffiti.pc | [Ermelinda DeLaViña’s Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) | “Graffiti.pc #N” means the catalogue’s conjecture number, including any lettered variant. This is not the original Written on the Wall catalogue. |
| Cazenave spectral | [Section 7 of the November 2026 preprint](https://arxiv.org/html/2611.03879v1#S7) | Use the paper's conjecture number and lettered part, plus corpus ID when given. |
| Erdős Problems | [Thomas F. Bloom's catalogue](https://www.erdosproblems.com/) | “Erdős Problem #N” uses the catalogue's numbering; partial results do not change the problem's open status. |

## AutoGraphForge

- [Ján Pastorek’s paper](https://arxiv.org/abs/2609.03478) describes the experiment and reports 6,522 survivors. The pinned normalized file removes 82 algebraic restatements, leaving 6,440 normalized statements.
- For audits, compare the [raw ranked list](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch.txt), [release records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json), [refutations](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_refuted.json), and [upstream verified proofs](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/verified_proofs). Use the stable release record ID as well as the normalized line when available.
- The [pinned Lean invariant definitions](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/lean_project/LeanProject/GraphInvariants.lean) and [pinned GraphCalc implementations](https://github.com/RandyRDavila/GraphCalc/tree/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants) help resolve definition and domain conventions.

## Graffiti³

- Paper DOI: [10.21203/rs.3.rs-8493329/v1](https://doi.org/10.21203/rs.3.rs-8493329/v1). See the [author's companion code and notebooks](https://github.com/RandyRDavila/TxGraffiti2/tree/main/papers/graffiti3) for the experiments. The paper, not notebook output or AutoGraphForge row numbers, controls the numbering here.

## Graffiti.pc

- The live catalogue serves separate [statements and statuses](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json), [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json), and [curator comments](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/comments.json). There is also a [printable snapshot](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).
- The [Written on the Wall II section of Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/main/FormalConjectures/WrittenOnTheWallII) is a useful secondary index of Lean statements. Check those against the catalogue's exact wording and definitions.

## Cazenave spectral graph conjectures

- [Tristan Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*, arXiv:2611.03879v1](https://arxiv.org/html/2611.03879v1#S7), is the pinned source for the paper's numbered conjectures and subparts. Its [proof and corpus archive](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip) is indexed by separate corpus IDs. Write both the paper locator and corpus ID when available; do not treat an unrefuted numerical candidate as verified open.
- Status checks on 2026-11-27: the paper's Conjecture 3 follows from [Arizmendi and Arizmendi's energy bound](https://arxiv.org/abs/2009.08041), since adjacency energy is at most rank times spectral radius. [A Lean proof of Conjecture 4](https://www.trureturing.org/research/op-cazenave2611c4/) is publicly recorded, and [Conjecture 5 has a reported exact Lean proof](https://www.trureturing.org/research/op-cazenave2611c5/) (not replayed here). [Kramer's proof of 6(ii)](https://hexagonmath.org/pdf/2611.00232v1) covers the exact paper statement; [6(iii) has a posted proposed proof](https://hexagonmath.org/2611.01102v1), not independently checked here. The exact 6(i) inequality is [formalized in this repository](cazenave-6i/); it and the edge-count half of 6(iv) follow from older, stronger bounds of [Elphick–Wocjan](https://arxiv.org/abs/1508.07950) and [Stanley](https://math.mit.edu/~rstan/pubs/pubfiles/71.pdf). The separate adjacency-rank half of 6(iv) is [proved in Lean in this repository](cazenave-6iv-rank/), with equality precisely for K₂; no exact earlier settlement was found in the bounded search. Do not claim these previously resolved targets as new.

A release's “proposed,” “survivor,” or “open” label is not evidence of novelty. Check dated prior work and exact definitions before claiming a new resolution.

## Erdős Problems

- [Thomas F. Bloom's catalogue](https://www.erdosproblems.com/) controls the numbering. Check the [pinned community status data](https://github.com/teorth/erdosproblems/blob/3d9fd1caec27bb400ff4a92a513a29965bd99695/data/problems.yaml), the exact statement, and primary literature before claiming novelty. A catalogue status is not conclusive evidence that a result is new.
- [#324: distinct polynomial pair sums](https://www.erdosproblems.com/324), open in the pinned data. [Dubickas and Novikas](https://doi.org/10.1002/mana.202000334) excluded degree at most three. The [even-quartic collision certificates](erdos-324-even-quartic-collisions/) are a restricted partial result, not a solution.
- [#291: harmonic numbers and least common multiples](https://www.erdosproblems.com/291), investigate the open infinitude question for the cases where the reduced harmonic denominator equals the LCM. The other direction is known; distinguish it from the open half. See [Shiu](https://arxiv.org/abs/1607.02863) and [van Doorn](https://arxiv.org/abs/2411.03073).
