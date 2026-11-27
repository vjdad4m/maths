import LowOmissions
namespace Graffiti384b.Adjacent15
open Finset SimpleGraph EarFrame33
open private Repair.nbr_mono Repair.full_nbr Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem with_third {P Q : Finset V} (fr : Frame G P Q)
    {f u v : V} (fm : f∈P∪Q) (df : G.degree f=2) (du : G.degree u=2)
    (dv : G.degree v=2) (uv : G.Adj u v) (uf : u≠f) (vf : v≠f) : gamma G≤bound G := by
  classical
  let S := insert f (high G)
  have low {i : V} (di : G.degree i=2) : i∉high G := by
    intro m; have := (mem_filter.mp m).2; omega
  have us : u∉S := by simp [S,uf,low du]
  have vs : v∉S := by simp [S,vf,low dv]
  have size : S.card=(high G).card+1 := card_insert_of_not_mem (low df)
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut G P Q fr.1
  let L := S∩A
  let R := S\A
  have free (i : V) (im : i∈S) (ip : i∉P) (iq : i∉Q) : 3≤G.degree i := by
    rcases mem_insert.mp im with rfl|h
    · exact False.elim ((mem_union.mp fm).elim ip iq)
    · exact (mem_filter.mp h).2
  have left (i : V) (im : i∈L) : 2≤nbr G i Lᶜ := by
    obtain ⟨is,ia⟩ := mem_inter.mp im
    have enough : 2≤nbr G i Aᶜ := by
      by_cases ip : i∈P
      · exact (fr.2.1 i ip).trans (Repair.nbr_mono G _ qb)
      have := free i is ip (fun iq => mem_compl.mp (qb iq) ia)
      have := la i ia ip
      have := Repair.full_nbr G i A
      omega
    exact enough.trans (Repair.nbr_mono G _ (compl_subset_compl.mpr inter_subset_right))
  have right (i : V) (im : i∈R) : 2≤nbr G i Rᶜ := by
    obtain ⟨is,ia⟩ := mem_sdiff.mp im
    have enough : 2≤nbr G i A := by
      by_cases iq : i∈Q
      · exact (fr.2.2 i iq).trans (Repair.nbr_mono G _ pa)
      have := free i is (fun ip => ia (pa ip)) iq
      have := rb i (mem_compl.mpr ia) iq
      have := Repair.full_nbr G i A
      omega
    exact enough.trans (Repair.nbr_mono G _ (fun _ h => mem_compl.mpr (fun m => (mem_sdiff.mp m).2 h)))
  have split : Split G S := ⟨L,R,disjoint_left.mpr (fun _ m h => (mem_sdiff.mp h).2 (mem_inter.mp m).2),
    by ext i; simp only [L,R,mem_union,mem_inter,mem_sdiff]; tauto,left,right⟩
  apply (split.adjoin G du uv vs).exact
  rw [card_insert_of_not_mem us,size]
  have := type_bound G
  omega

/-- At every order and diversity, an adjacent degree-two pair and any degree-two
vertex in a protected frame imply the catalogue bound. The framed vertex may
belong to the pair. -/
theorem exact_of_frame {P Q : Finset V} (fr : Frame G P Q) {f u v : V}
    (fm : f∈P∪Q) (df : G.degree f=2) (du : G.degree u=2) (dv : G.degree v=2)
    (uv : G.Adj u v) : gamma G≤bound G := by
  classical
  by_contra! bad
  have mate {i j : V} (im : i∈P∪Q) (di : G.degree i=2) (ij : G.Adj i j) : j∈P∪Q := by
    have allN (D : Finset V) (two : 2≤nbr G i D) : j∈D := by
      have sub : D.filter (G.Adj i)⊆G.neighborFinset i := fun w m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2
      have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,di]; exact two)
      exact (mem_filter.mp (eq.symm ▸ (G.mem_neighborFinset ..).mpr ij)).1
    exact (mem_union.mp im).elim (fun h => mem_union_right _ (allN Q (fr.2.1 i h)))
      (fun h => mem_union_left _ (allN P (fr.2.2 i h)))
  have sparse := Squares29.sparse G bad P Q fr
  by_cases uf : u=f
  · subst f; exact uv.ne (sparse u fm v (mate fm du uv) du dv)
  by_cases vf : v=f
  · subst f; exact uv.ne (sparse u (mate fm dv uv.symm) v fm du dv)
  exact (not_lt_of_ge (with_third G fr fm df du dv uv uf vf)) bad

/-- In particular no degree-two vertex of a counterexample containing an adjacent
degree-two pair can lie on a four-cycle. -/
theorem exact_of_square {f x u v : V} (sq : Squares29.Opposite G f x)
    (du : G.degree u=2) (dv : G.degree v=2) (uv : G.Adj u v) : gamma G≤bound G :=
  exact_of_frame G (Squares29.frame G sq) (mem_union_left _ (mem_insert_self ..)) sq.1 du dv uv

end Graffiti384b.Adjacent15
#print axioms Graffiti384b.Adjacent15.exact_of_frame
#print axioms Graffiti384b.Adjacent15.exact_of_square
