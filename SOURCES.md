# Conjecture sources

The [problem index](README.md) records results in this repository. The links below identify the original statements and their numbering. The three numbering systems are separate.

| Collection | Where to find the problems | How to interpret the index |
| --- | --- | --- |
| AutoGraphForge | [Pinned normalized survivor list](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt) | “AutoGraphForge line N” means physical line N in this exact file, not a conjecture number in another collection. |
| Graffiti³ | [Randy Davila’s Graffiti³ paper, Research Square v1](https://assets-eu.researchsquare.com/files/rs-8493329/v1_covered_f3b2ebd5-1eff-4ba6-aa7a-671608894aaf.pdf) | “Graffiti³ #N” means the numbered conjecture in this paper, including lettered parts where applicable. |
| Graffiti.pc | [Ermelinda DeLaViña’s Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) | “Graffiti.pc #N” means the catalogue’s conjecture number, including any lettered variant. This is not the original Written on the Wall catalogue. |

## AutoGraphForge

- [Ján Pastorek’s paper](https://arxiv.org/abs/2609.03478) describes the experiment and reports 6,522 survivors. The pinned normalized file removes 82 algebraic restatements, leaving 6,440 normalized statements.
- For audits, compare the [raw ranked list](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch.txt), [release records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json), [refutations](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_refuted.json), and [upstream verified proofs](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/verified_proofs). Use the stable release record ID as well as the normalized line when available.
- The [pinned Lean invariant definitions](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/lean_project/LeanProject/GraphInvariants.lean) and [pinned GraphCalc implementations](https://github.com/RandyRDavila/GraphCalc/tree/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants) help resolve definition and domain conventions.

## Graffiti³

- Paper DOI: [10.21203/rs.3.rs-8493329/v1](https://doi.org/10.21203/rs.3.rs-8493329/v1). See the [author's companion code and notebooks](https://github.com/RandyRDavila/TxGraffiti2/tree/main/papers/graffiti3) for the experiments. The paper, not notebook output or AutoGraphForge row numbers, controls the numbering here.

## Graffiti.pc

- The live catalogue serves separate [statements and statuses](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json), [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json), and [curator comments](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/comments.json). There is also a [printable snapshot](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).
- The [Written on the Wall II section of Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/main/FormalConjectures/WrittenOnTheWallII) is a useful secondary index of Lean statements. Check those against the catalogue's exact wording and definitions.

A release's “proposed,” “survivor,” or “open” label is not evidence of novelty. Check dated prior work and exact definitions before claiming a new resolution.
