# Graffiti.pc #235

[Graffiti.pc catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/), with the [exact statements](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json).

## #235: Periphery bound with bipartite bonus

Let t=γ_t(G) be the total domination number of a finite simple connected graph of order at least two, let B be the set of vertices of maximum eccentricity, and let e=max_z dist(z,B), with e=0 if B=V. The claim is t≥2e/3+1 if G is bipartite, and t≥2e/3 otherwise.

[Henning and Yeo, Discrete Applied Mathematics 173 (2014), pp. 45–52](https://doi.org/10.1016/j.dam.2014.03.013) proved t≥(3e+2)/4, also recorded under catalogue #233. This implies the nonbipartite bound and implies the bipartite bound for e≥6. For e=3,4,5 the integer lower bounds are 3,4,5 respectively and suffice; e≤1 follows from t≥2.

Suppose G is bipartite and e=2. If t=2, a dominating edge xy meets both parts, each of its ends adjacent to the entire opposite part. If G is complete bipartite, every nonperipheral vertex is within distance one of B (only a singleton part can contain such a vertex). Otherwise G has diameter three, and a vertex that misses any opposite-part neighbor is peripheral, since that missed pair is at distance three via xy. There is a peripheral vertex in each part (the endpoints of a missing cross edge). Thus every nonperipheral vertex, being adjacent to the entire opposite part, is adjacent to B. In either case e≤1, a contradiction. Therefore t≥3, sufficient when e=2. This is a short deduction from a substantial published theorem, not a claim the theorem is new.

## Verification scope

The graph argument is a written proof, not a full Lean formalization.

AI-assisted work shared for review. No priority claim is made.
