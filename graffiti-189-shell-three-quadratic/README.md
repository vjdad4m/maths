# Universal shell-three parity bound

For any finite connected simple graph in which every vertex has at most d
vertices at distance exactly two, each vertex has at most floor((d+1)^2/4)
vertices at distance exactly three. Lean checks the equivalent scaled
inequality 4·|Shell3(x)|≤(d+1)^2. In particular d=5 gives at most nine.

Choose a minimum subset of the neighbors of x that covers all distance-two
vertices. Each chosen neighbor (donor) has a private covered vertex. An
other donor costs one slot in the distance-two budget at any fixed donor:
charge its private vertex if adjacent, otherwise charge the other donor
itself via x. These charges are distinct and exclude shell-three vertices.
Thus a cover of size m charges the third shell to at most m(d+1−m).

This graph lemma imports only SmallSeparator189 and Mathlib, not the
more extensive #189 connectivity proofs. Lean 4.19 with warnings-as-errors;
the theorem prints only the three standard axioms.
