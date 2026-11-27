# Local independence and induced paths: partial results for Graffiti.pc #133

**Neither reading of the full conjecture is proved here.** The [catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) uses square brackets around the local-independence average. This package distinguishes the floor reading from the stronger unrounded reading in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/WrittenOnTheWallII/GraphConjecture133.lean). For a graph with no four-cycle, these ask for an induced path of order at least $r+\lfloor a\rfloor$ and $r+a$, respectively, where $r$ is radius and $a$ is average neighborhood independence. If a four-cycle exists, both ask for at least $r+1$. Cycle exclusions refer to ordinary subgraphs, not just induced cycles.

## Checked cases

- **Floor reading, $\lfloor a\rfloor\le3$:** all radii, except possibly radius three with a five-cycle. [Lean theorem](src/DensityBands133.lean).
- **Floor reading, no five-cycle:** every graph of radius at most two, and every graph of radius at most three with even $\lfloor a\rfloor$. [Lean theorems](src/RoundedBand133.lean).
- **Unrounded reading:** every graph with radius at most two and $a\le3$. [Lean theorem](src/RoundedBand133.lean).

A five-cycle inside a connected four-cycle-free graph either forces an induced five-vertex path or is the whole graph. In the no-four/no-five-cycle class, local mean at least three gives an induced six-vertex path even without a connectivity hypothesis. [Five-cycle lemma](src/FiveCycle133.lean) · [Six-vertex path](src/SixCycle133.lean).

## The pruning argument

Write $\lambda_H(v)$ for neighborhood independence in a four-cycle-free graph $H$, and $S(H)=\sum_v\lambda_H(v)$. Deleting $v$ decreases $S$ by at most $2\lambda_H(v)$. Indeed a neighbor $x$ can lose at most one unit, and loses none if $xv$ lies in a triangle: in an independent subset of $N(x)$ containing $v$, the other triangle vertex can replace $v$. The neighbors joined to $v$ by edges not in triangles form an independent subset of $N(v)$.

Thus $S(H)\ge2d|H|$ is preserved while pruning vertices with $\lambda_H(v)\le d$. It yields a nonempty induced subgraph with minimum local independence at least $d+1$, even when local independence and degree vary substantially. When five-cycles are also absent, the induced-path endpoint bound gives a path on at least $2d+3$ vertices there. [Lean pruning and density lemmas](src/LocalDensity133.lean).

The high-radius case uses Chung's bound for a longest induced path, as credited and reported by [Erdős, Saks, and Sós, Theorem 2.2](https://www.renyi.hu/~p_erdos/1986-08.pdf). The proof makes no priority claim for the new scope.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-133-density/replay.sh
