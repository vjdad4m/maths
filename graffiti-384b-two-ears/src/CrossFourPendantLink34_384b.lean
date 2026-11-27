import CrossFourPins34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph LowSample
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem pendant_link
    {e z a b : V} (ez : e≠z) (ears : twos G={e,z}) (q : (types G).card≤(nonleaves G).card)
    (hi : G.neighborFinset e∪G.neighborFinset z⊆high G)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset z))
    (ear : G.neighborFinset e={a,b}) (ab : G.Adj a b) (priv : G.neighborFinset a∩G.neighborFinset b={e})
    (miss : ∀ j∈G.neighborFinset z,¬G.Adj a j) (hit : ∀ j∈G.neighborFinset z,G.Adj b j) (fail : bound G<gamma G) :
    ∀ x∈G.neighborFinset a,nbr G x (G.neighborFinset a)≤1 := by
  classical
  have zt : z∈twos G := ears ▸ mem_insert_of_mem (mem_singleton_self _)
  let N := G.neighborFinset z
  let P := insert e N
  let Q : Finset V := {a,b,z}
  have ae : a∈G.neighborFinset e := ear ▸ mem_insert_self ..
  have be : b∈G.neighborFinset e := ear ▸ mem_insert_of_mem (mem_singleton_self _)
  have ea := (G.mem_neighborFinset _ _).mp ae
  have eb := (G.mem_neighborFinset _ _).mp be
  have an : a∉N := fun m => disjoint_left.mp sep ae m
  have bn : b∉N := fun m => disjoint_left.mp sep be m
  have az : ¬G.Adj a z := fun edge => an ((G.mem_neighborFinset _ _).mpr edge.symm)
  have bz : b≠z := fun eq => (mem_sdiff.mp zt).2 (eq ▸ hi (mem_union_left _ be))
  have aq : a∈Q := mem_insert_self ..
  have bq : b∈Q := mem_insert_of_mem (mem_insert_self ..)
  have zq : z∈Q := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have pn : N⊆P := subset_insert ..
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr; intro v vp vq
    simp only [Q,mem_insert,mem_singleton] at vq
    rcases mem_insert.mp vp with rfl|vn
    · exact vq.elim ea.ne (fun o => o.elim eb.ne ez)
    · rcases vq with rfl|rfl|rfl
      · exact an vn
      · exact bn vn
      · exact G.not_mem_neighborFinset_self _ vn
  have low : twos G⊆P∪Q := ears ▸ insert_subset (mem_union_left _ (mem_insert_self ..)) (singleton_subset_iff.mpr (mem_union_right _ zq))
  have pg (v : V) (vp : v∈P) : 2≤nbr G v Q := by
    rcases mem_insert.mp vp with rfl|vn
    · exact PinnedColor34.two G ab.ne ea eb aq bq
    · exact PinnedColor34.two G bz (hit v vn).symm ((G.mem_neighborFinset _ _).mp vn).symm bq zq
  have qg (v : V) (vq : v∈Q) (va : v≠a) : 2≤nbr G v P := by
    have bOr : v=b ∨ v=z := by simpa [Q,va] using vq
    have inc : N⊆P.filter (G.Adj v) := by
      intro j jm; apply mem_filter.mpr ⟨pn jm,?_⟩
      exact bOr.elim (fun eq => eq ▸ hit j jm) (fun eq => eq ▸ (G.mem_neighborFinset _ _).mp jm)
    have nc : N.card=2 := (card_neighborFinset_eq_degree _ _).trans (LowSample.two_degree G zt)
    exact nc ▸ card_le_card inc
  have thin (x : V) (xn : x∈G.neighborFinset a) : nbr G x (G.neighborFinset a)≤1 := by
    by_contra! many
    obtain ⟨i,im⟩ := card_pos.mp (show 0<((G.neighborFinset a).filter (G.Adj x)).card by exact Nat.zero_lt_one.trans many)
    obtain ⟨j,jm,ji⟩ := exists_ne_of_one_lt_card many i
    have ax := (G.mem_neighborFinset _ _).mp xn
    have xe : x≠e := by
      intro eq
      have one (r : V) (m : r∈(G.neighborFinset a).filter (G.Adj x)) : r=b := by
        have er : G.Adj e r := eq ▸ (mem_filter.mp m).2
        have rr := (G.mem_neighborFinset _ _).mpr er
        rw [ear,mem_insert,mem_singleton] at rr
        exact rr.resolve_left ((G.mem_neighborFinset _ _).mp (mem_filter.mp m).1).ne.symm
      exact ji ((one j jm).trans (one i im).symm)
    have xp : x∉P := fun m => (mem_insert.mp m).elim xe (fun xn => miss x xn ax)
    have out (r : V) (rm : r∈(G.neighborFinset a).filter (G.Adj x)) : r∉Q := by
      have ar := (G.mem_neighborFinset _ _).mp (mem_filter.mp rm).1
      intro rq
      simp only [Q,mem_insert,mem_singleton] at rq
      rcases rq with ra|rb|rz
      · exact ar.ne ra.symm
      · have bx : G.Adj b x := rb ▸ (mem_filter.mp rm).2.symm
        have cm := mem_inter.mpr ⟨xn,(G.mem_neighborFinset _ _).mpr bx⟩
        rw [priv,mem_singleton] at cm
        exact xe cm
      · exact az (rz ▸ ar)
    exact (not_lt_of_ge (fork G aq dis low q pg qg xp (out i im) (out j jm) ax
      ((G.mem_neighborFinset _ _).mp (mem_filter.mp im).1) ((G.mem_neighborFinset _ _).mp (mem_filter.mp jm).1)
      (mem_filter.mp im).2 (mem_filter.mp jm).2 ji.symm)) fail
  exact thin
end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.pendant_link
