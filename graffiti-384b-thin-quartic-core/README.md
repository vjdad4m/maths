# Graffiti.pc #384b at 29 triangle counts and 28 nonleaves

Let $G$ be a finite simple graph with exactly 29 distinct vertex triangle-incidence counts and exactly 28 vertices of degree at least two. Zero counts are included when realized. Let $H$ be induced by those 28 vertices. In a hypothetical failure all their counts are positive and pairwise distinct. The spanning graph $J$ on $H$ retains the edges that belong to triangles. It has a unique degree-two vertex $e$, and its neighbors $p,q$ are adjacent. All neighborhoods, degrees and cliques below are measured in $J$.

**If $J$ has no five-clique, the catalogue bound holds in either of two cases.**

1. The only common neighbor of $p,q$ is $e$.
2. Some common neighbor of $p,q$ other than $e$ has degree four.

In either case $G$ has a 2-dominating set of size at most $|V(G)|-15$. Every vertex outside that set has at least two neighbors in it. The original-graph theorems apply at every order and do not require connectivity. [No ear square](ThinFinish28.lean) · [Quartic fourth vertex](QuarticFinish28.lean)

## Two complementary samples for the first case

Write $W=V(J)\setminus\{e,p,q\}$, of size 25. In the first trial keep both endpoints and choose eight members of $W$. In the second keep the ear and choose ten members of $W$. After each choice, add each omitted vertex with fewer than two retained neighbors. If $\gamma_2(J)\ge14$, at least four vertices need repair on every first trial and three on every second trial. Weighting the first family by three gives a total deficit of at least $3\cdot4\binom{25}{8}+3\binom{25}{10}=22{,}785{,}180$. [Trial and fiber bounds](ThinTrial28.lean)

An exterior vertex has zero or one neighbor among the endpoints. If it has one, it receives an automatic neighbor in the first trial and loses access to that neighbor in the second. The two bounds are evaluated at the same actual degree. Each contact is charged 205,000 at the exterior vertex and credited once at its endpoint. If an endpoint has $a$ exterior neighbors, at most $\binom{25-a}{10}$ second trials miss all of them. Its triangle count is at most $1+\binom{a}{2}$, since the only triangle using its other endpoint is the ear triangle. The five-clique-free neighborhood bound controls the exterior vertices. [Geometric inequalities](ThinCharges28.lean)

The 27 vertices other than $e$ have distinct counts of at least two. Lean checks the rank and degree inequalities for every possible rank and degree. The sum of the 27 charges is 26,237,251. Each endpoint returns at least 1,734,380 after balancing contacts. Thus the repair mass is at most **22,768,491**, below the required total by **16,689**. The finite table certifies inequalities for all graphs satisfying the hypotheses. [Integer certificate](ThinTable28.lean) · [Aggregation](ThinFinish28.lean)

## Two forced discounts for a quartic square

Suppose a quartic fourth vertex $s$ survives the predecessor exclusions. Its count must be four. Its neighbors are $p,q,x,y$, where $x$ misses both endpoints and $y$ sees both. Since $p,q$ have different triangle counts, some exterior vertex $t$ sees exactly one endpoint. Otherwise their exterior neighborhoods and the expressions for their counts would agree. The vertex $t$ differs from $x,y,s$ and loses no neighbor when $e,s$ are omitted. [Distinguishing contact](QuarticContact28.lean) · [Frozen geometry](graff384b-four28-sources.zip)

Retain $p,q$ and sample nine of the remaining 24 vertices after deleting $e,s$. The old maximum charge with one exception is 3,958,086. The vertex $y$ always has two retained neighbors and refunds at least 29,029. The vertex $t$ already has one at its original degree and refunds at least 24,024. The resulting maximum of **3,905,033** is below $3\binom{24}{9}=3{,}922{,}512$ by **17,479**. The predecessor's discounted repair theorem is used in the sample argument. Its extra adjacent-failure saving can be zero here. [Two discounts](QuarticCredits28.lean) · [Lift through the induced subgraph](QuarticFinish28.lean)

## Remaining scope

In a surviving five-clique-free graph of this profile, at least one ear square exists. Every fourth vertex has degree at least five and triangle count at least three. There is an induced five-clique minus one edge disjoint from the ear triangle. Among vertices outside both configurations there are cubic vertices of counts two and three, or there is exactly one cubic vertex there. In the latter case there is exactly one fourth vertex on an ear square. It lies in the central triangle of that induced graph, and the external cubic sees the other two central vertices and misses this one. The theorem leaves these configurations open, as well as the branch containing a five-clique and the other diversity and nonleaf counts. [Exact residual statement](SquareResidual28.lean)

## Replay

Build the [28-nonleaf ear-square package](../graffiti-384b-core28-ear-squares/) and its documented dependencies with Lean 4.19.0 and Mathlib 4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With those objects on the Lean search path, check `sha256sum -c NEW-SOURCES.sha256` and compile the eight extension modules in `modules.txt` order with synchronous elaboration and warnings as errors. The [recorded replay](StrictEar28.log) authenticated 280 predecessor sources and their objects and reports only propext, Classical.choice, and Quot.sound for 18 declarations. No recursive cold rebuild was recorded.
