import Rooted185

namespace Graffiti185.Cut
open SimpleGraph Finset
set_option maxHeartbeats 1400000
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq I] in
lemma union_of_root_card [Nonempty I] (r : V) (label : V → I) (S : I → Finset V)
    (hr : ∀ i, r ∈ S i) (hl : ∀ i v, v ∈ S i → v ≠ r → label v = i) :
    (univ.biUnion S).card + Fintype.card I = (∑ i, (S i).card) + 1 := by
  classical
  let T (i : I) := (S i).erase r
  have hdis : (univ : Finset I).toSet.PairwiseDisjoint T := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro v hi hj
    obtain ⟨hnr,hi'⟩ := mem_erase.mp hi
    exact hne ((hl i v hi' hnr).symm.trans (hl j v (mem_erase.mp hj).2 hnr))
  have he : (univ.biUnion S).erase r = univ.biUnion T := by
    ext v
    simp only [T, mem_erase,mem_biUnion,mem_univ,true_and]
    exact ⟨fun ⟨hv,i,hi⟩ => ⟨i,hv,hi⟩,fun ⟨i,hv,hi⟩ => ⟨hv,i,hi⟩⟩
  have h := Finset.card_biUnion hdis
  rw [←he] at h
  have hroot : r ∈ univ.biUnion S :=
    mem_biUnion.mpr ⟨Classical.choice ‹Nonempty I›,mem_univ _,hr _⟩
  have hsu : (∑ i, (S i).card) = (∑ i, (T i).card) + Fintype.card I := by
    calc
      _ = ∑ i, ((T i).card + 1) := Finset.sum_congr rfl fun i _ =>
        (Finset.card_erase_add_one (hr i)).symm
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hroot' := Finset.card_erase_add_one hroot
  omega

omit [Fintype V] [DecidableEq I] in
lemma con_union_rooted [Nonempty I] (G : SimpleGraph V) (r : V) (D : I → Finset V)
    (hr : ∀ i, r ∈ D i) (hcon : ∀ i, Graffiti177.Con G (D i)) :
    Graffiti177.Con G (univ.biUnion D) := by
  classical
  let U := univ.biUnion D
  have sub (i : I) : D i ⊆ U := fun _ h => mem_biUnion.mpr ⟨i,mem_univ _,h⟩
  have hroot : r ∈ U := sub (Classical.choice ‹Nonempty I›) (hr _)
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨r,hroot⟩,?_⟩
  intro v
  obtain ⟨i,_,hvi⟩ := mem_biUnion.mp v.prop
  let f := (G.induceHomOfLE (show (D i : Set V) ≤ ↑U from sub i)).toHom
  exact ((hcon i).preconnected (⟨r,hr i⟩ : (D i : Set V)) ⟨v,hvi⟩).map f

structure RootData (G : SimpleGraph V) (r : V) (label : V → I) (i : I) where
  D : Finset V
  B : Finset V
  rootD : r ∈ D
  rootB : r ∈ B
  con : Graffiti177.Con G D
  dom : ∀ v, v ≠ r → label v = i → v ∉ D → Graffiti177.Dominates G D v
  inD : ∀ v ∈ D, v ≠ r → label v = i
  inB : ∀ v ∈ B, v ≠ r → label v = i
  color : V → Bool
  colorRoot : color r = false
  diff : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → color v ≠ color w
  budget : D.card + 1 ≤ B.card

omit [DecidableEq I] in
theorem glued_bound_gain [Nonempty I] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (label : V → I) (hsep : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    (P : ∀ i, RootData G r label i) (gain : I → ℕ)
    (hg : ∀ i, (P i).D.card + gain i ≤ (P i).B.card) :
    Fintype.card V + (∑ i, gain i) ≤ Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G := by
  classical
  let D (i : I) := (P i).D
  let B (i : I) := (P i).B
  let U := univ.biUnion D
  let T := univ.biUnion B
  have dsub (i : I) : D i ⊆ U := fun _ h => mem_biUnion.mpr ⟨i,mem_univ _,h⟩
  have rootU : r ∈ U := dsub (Classical.choice ‹Nonempty I›) (P _).rootD
  have dom : ∀ v ∉ U, Graffiti177.Dominates G U v := by
    intro v hv
    have hvn : v ≠ r := fun e => hv (e.symm ▸ rootU)
    obtain ⟨w,hw,he⟩ := (P (label v)).dom v hvn rfl (fun m => hv (dsub _ m))
    exact ⟨w,dsub _ hw,he⟩
  have Hcon := con_union_rooted G r D (fun i => (P i).rootD) (fun i => (P i).con)
  have lf := (Graffiti177.conDom_leaves G U Hcon dom).trans (Graffiti185.Reuse.leaves_bridge G)
  change (univ \ U).card ≤ Graffiti185.maxLeaves G at lf
  let χ (v : V) : Bool := if v = r then false else (P (label v)).color v
  have restriction (i : I) (v : V) (hv : v ∈ B i) : χ v = (P i).color v := by
    by_cases h : v = r
    · subst v
      simp [χ,(P i).colorRoot]
    · have he := (P i).inB v hv h
      simp only [χ,if_neg h]
      exact congrArg (fun j => (P j).color v) he
  have bicol : ∀ v w : T, G.Adj v.val w.val → χ v.val ≠ χ w.val := by
    intro v w e
    obtain ⟨i,_,hvi⟩ := mem_biUnion.mp v.prop
    obtain ⟨j,_,hwj⟩ := mem_biUnion.mp w.prop
    by_cases hv : v.val = r
    · have hvj : v.val ∈ B j := hv.symm ▸ (P j).rootB
      rw [restriction j v hvj,restriction j w hwj]
      exact (P j).diff v hvj w hwj e
    by_cases hw : w.val = r
    · have hwi : w.val ∈ B i := hw.symm ▸ (P i).rootB
      rw [restriction i v hvi,restriction i w hwi]
      exact (P i).diff v hvi w hwi e
    have hij : i = j := ((P i).inB v hvi hv).symm.trans
      ((hsep v w hv hw e).trans ((P j).inB w hwj hw))
    subst j
    rw [restriction i v hvi,restriction i w hwj]
    exact (P i).diff v hvi w hwj e
  have hT : T.card ≤ Graffiti185.bipartiteNumber G := by
    apply le_trans _ (Graffiti185.Reuse.bipartite_bridge G)
    let A := T.filter (fun v => χ v = false)
    let C := T.filter (fun v => χ v = true)
    have dis : Disjoint A C := Finset.disjoint_left.mpr (by
      intro x hx hx'
      have h1 := (mem_filter.mp hx).2
      have h2 := (mem_filter.mp hx').2
      change χ x = false at h1
      change χ x = true at h2
      simp [h1] at h2)
    have cv : A ∪ C = T := by
      ext v
      simp only [A,C,mem_filter,mem_union]
      cases χ v <;> simp
    have hf : Short177.Indep G A := by
      intro x hx y hy _ he
      have ⟨xt,hf⟩ := mem_filter.mp hx
      have ⟨yt,hf'⟩ := mem_filter.mp hy
      exact bicol ⟨x,xt⟩ ⟨y,yt⟩ he (hf.trans hf'.symm)
    have ht : Short177.Indep G C := by
      intro x hx y hy _ he
      have ⟨xt,hf⟩ := mem_filter.mp hx
      have ⟨yt,hf'⟩ := mem_filter.mp hy
      exact bicol ⟨x,xt⟩ ⟨y,yt⟩ he (hf.trans hf'.symm)
    unfold Short177.bipartiteNum
    exact le_sup (s := univ.filter (Short177.TwoColor G)) (f := Finset.card)
      (mem_filter.mpr ⟨mem_univ _,A,C,dis,cv,hf,ht⟩)
  have hC1 := union_of_root_card r label D (fun i => (P i).rootD) (fun i => (P i).inD)
  have hC2 := union_of_root_card r label B (fun i => (P i).rootB) (fun i => (P i).inB)
  change U.card + Fintype.card I = (∑ i, (D i).card) + 1 at hC1
  change T.card + Fintype.card I = (∑ i, (B i).card) + 1 at hC2
  have hu : U.card + (∑ i, gain i) ≤ T.card := by
    have ht : (∑ i, ((D i).card + gain i)) ≤ ∑ i, (B i).card :=
      Finset.sum_le_sum fun i _ => hg i
    rw [Finset.sum_add_distrib] at ht
    omega
  have hc := card_sdiff_add_card_eq_card (subset_univ U)
  rw [card_univ] at hc
  omega

omit [DecidableEq I] in
theorem glued_bound [Nonempty I] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (label : V → I) (hsep : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    (P : ∀ i, RootData G r label i) :
    Fintype.card V + Fintype.card I ≤ Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G := by
  have hs : (∑ _i : I, 1 : ℕ) = Fintype.card I := by simp
  rw [←hs]
  exact glued_bound_gain G r label hsep P (fun _ => 1) (fun i => (P i).budget)

#print axioms glued_bound_gain
#print axioms glued_bound
end Graffiti185.Cut
