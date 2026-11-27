import Recolor34_384b
import LowSample384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph LowSample
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Protect the last pin a with two leaves around x in its neighborhood. -/
theorem fork {P Q : Finset V} {a x i j : V} (aq : a∈Q) (sep : Disjoint P Q)
    (low : twos G⊆P∪Q) (q : (types G).card≤(nonleaves G).card)
    (pg : ∀ v∈P,2≤nbr G v Q) (qg : ∀ v∈Q,v≠a → 2≤nbr G v P)
    (xp : x∉P) (iq : i∉Q) (jq : j∉Q) (ax : G.Adj a x)
    (ai : G.Adj a i) (aj : G.Adj a j) (xi : G.Adj x i) (xj : G.Adj x j) (ij : i≠j) : gamma G≤bound G := by
  let A := insert i (insert j P)
  let B := insert x Q
  have pa : P⊆A := (subset_insert _ _).trans (subset_insert _ _)
  have qb : Q⊆B := subset_insert ..
  have ia : i∈A := mem_insert_self ..
  have ja : j∈A := mem_insert_of_mem (mem_insert_self ..)
  have xb : x∈B := mem_insert_self ..
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro v va vb
    rcases mem_insert.mp vb with rfl|vq
    · rcases mem_insert.mp va with eq|vl
      · exact xi.ne eq
      · rcases mem_insert.mp vl with eq|p
        · exact xj.ne eq
        · exact xp p
    · rcases mem_insert.mp va with rfl|vl
      · exact iq vq
      · rcases mem_insert.mp vl with rfl|p
        · exact jq vq
        · exact disjoint_left.mp sep p vq
  apply PinnedColor34.complete G dis q
  · intro v vn na nb
    by_contra! sm
    have ins := low (mem_sdiff.mpr ⟨vn,fun vh => (not_lt_of_ge (mem_filter.mp vh).2) sm⟩)
    exact (mem_union.mp ins).elim (fun p => na (pa p)) (fun q0 => nb (qb q0))
  · intro v va
    rcases mem_insert.mp va with rfl|vl
    · exact PinnedColor34.two G ax.ne ai.symm xi.symm (qb aq) xb
    · rcases mem_insert.mp vl with rfl|vp
      · exact PinnedColor34.two G ax.ne aj.symm xj.symm (qb aq) xb
      · exact (pg v vp).trans (Repair.nbr_mono G v qb)
  · intro v vb
    rcases mem_insert.mp vb with rfl|vq
    · exact PinnedColor34.two G ij xi xj ia ja
    · by_cases eq : v=a
      · exact eq ▸ PinnedColor34.two G ij ai aj ia ja
      · exact (qg v vq eq).trans (Repair.nbr_mono G v pa)
end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.fork
