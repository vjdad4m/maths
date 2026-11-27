# Graffiti.pc #189 when vertex connectivity is at least the second degree minus one

Let $G$ be a finite simple connected graph and let $d\ge3$. Suppose every two distinct vertices include one of degree at least $d$, and every vertex has at most $d+1$ vertices at even graph distance, with itself counted. If deleting fewer than $d-1$ vertices always leaves a connected graph, then $G$ has a Hamiltonian path.

For Graffiti.pc #189, take $d$ to be the second-smallest degree, with ties counted. **The conjecture remains open in general.** This note handles $d\ge3$ and connectivity at least $d-1$; it does not assume that the conjecture can be reduced to that range. It extends the [degree-three proof](../graffiti-189), using the same rotation and separator lemmas.

## Argument

Assume a longest path $P$ is not spanning. Rotate it if necessary so its endpoints both have degree at least $d$. Write $H$ for the graph induced by the omitted vertices. A vertex of $H$ is active if it has a neighbor on $P$. The tight separator argument gives each active vertex exactly one such neighbor, called its pin, and eccentricity at most three. The omitted graph is connected, and distinct pins are at least three positions apart on $P$. A pin's two flanks are its predecessor and successor on the path. Rotation rigidity gives
$|P|\ge4d-3$ and $|H|\ge d$.

**The pin count is exact.** Connectivity gives at least $d-1$ distinct pins. Fix an active $x$ with pin $p$. Each other pin $q$ is within three steps of $x$. If a short route uses a path edge between pins, the tight separator at the active vertex turns that edge into a step between their porters in $H$: any pin adjacent to $p$ is represented by an active neighbor of $x$. A route between distinct pins through a nonpin path vertex cannot use two steps, since that vertex would have to be a common flank. Therefore, for every $q\ne p$, an active vertex with pin $q$ is within two steps of $x$ in $H$. If any such vertex is adjacent to $x$, charge $q$ itself as a distance-two vertex from $x$; otherwise charge a $q$-porter at distance two. The charges are distinct and different from the two flanks of $p$. The bound of $d$ distance-two vertices gives at most $d-1$ pins. Thus there are exactly $d-1$, and the charges exhaust the budget.

**Every omitted vertex is active.** A path neighbor of a pin is either a flank or another pin. If an inactive vertex $u$ touched an active vertex $x$, every path vertex outside the pins and their flanks would be at distance exactly four from $u$. It is at most four via $x$. A shorter route from $u$ would need at least two steps to enter $P$ at a pin, and then it could not reach a vertex beyond the pin and its path neighbors in a single step. There are at least $(4d-3)-3(d-1)=d$ such path vertices. They and the pin of $x$ at distance two exceed $u$'s positive even-distance budget. Connectedness of $H$ now rules out any inactive vertex.

**Pin classes force a degree contradiction.** Porters with the same pin form a clique: a missing edge between them would create an uncharged distance-two vertex via their pin. Two classes are complete or anticomplete to one another. One cross edge, together with the class cliques, would otherwise give a porter a distance-two vertex of a pin it has already charged directly. For an anticomplete pair, each class must be a singleton: the two-step route from either class through an intermediate class reaches every member of the other, whereas the budget has room for only one such porter.

As $|H|\ge d$ and there are only $d-1$ classes, one class has at least two vertices and is complete to every other class. Its pin already has at least two distance-two vertices on $P$ (using endpoint rotation if the pin is next to an endpoint), so at most $d-2$ omitted vertices can be at distance two. Every porter outside the large class is at distance two from this pin. There are $d-2$ other classes, so all are singletons. A singleton porter has at most $d-2$ neighbors in $H$, since each consumes a distance-two slot at its pin, which also spends two slots on $P$. Thus its degree in $G$ is at most $d-1$. For $d\ge4$ there are at least two such low-degree vertices. For $d=3$ the singleton must touch both vertices in the large class, although it can have at most one neighbor in $H$. Both are contradictions.

## Sources

[Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) · [Easwar and Johari's partial results](https://arxiv.org/html/2609.11719v1). No priority claim is made.

## Lean and replay

The exact statement is [`traceable_near_connectivity`](src/AdjacentPins189.lean). It uses only standard Lean axioms and no finite graph search. Run from a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-189-near/replay.sh
