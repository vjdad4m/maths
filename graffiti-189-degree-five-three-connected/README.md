# Graffiti.pc #189: the degree-five threshold and 3-connectivity

Let G be a finite connected simple graph that stays connected after deleting
any set of fewer than three vertices. Assume all but at most one vertex have
degree at least five and that each even-distance set, including its own
center, has at most six vertices. Then G has a spanning path. This is a
complete subdomain of #189, with no order limit.

The earlier longest-path classification leaves an omitted high vertex with
one or two attachments. Its distance-three shell has at most nine vertices
by the published quadratic bound, so the remainder of the graph has little
room beyond the omitted star. A three-hook fan from the star to the longest
path goes through sufficient internal star paths to require more room in
both cases. The exceptional zero-length hooks can be retargeted through the
exact boundary. All paths and splices use the original graph.

[Main Lean theorem](FiveThreeHookFinal189.lean) · [Strict replay](StrictReplay.log)

The complete source archive includes the eleven modules and hashes of
the seven direct project imports. Build those earlier packages and their
dependencies using Lean and Mathlib v4.19.0, put their objects on LEAN_PATH,
and run the archived replay script. The short route and separated append
lemmas are localized from earlier verified repository proofs to avoid
importing overlapping declarations from independent predecessor chains.

This theorem does not settle the degree-five adjacent two-cut case or the
unrestricted conjecture.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
