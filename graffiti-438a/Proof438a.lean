import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Written on the Wall II, #438a. Independent formalization
of the arbitrary-subset bound in Siddhant Dubey's 2026 worklog.
Kuberwastaken independently proved #438b (Formal Conjectures #4915).
https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa
https://github.com/google-deepmind/formal-conjectures/issues/4915
-/

namespace Graffiti438

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def twoIndepNum (G : SimpleGraph V) : ℕ := by
  classical
  exact ((univ : Finset (Finset V)).filter
    (fun D : Finset V => (G.induce (↑D : Set V)).maxDegree ≤ 1)).sup Finset.card

omit [Fintype V] [DecidableEq V] in
private theorem unique_adj_on_dissociation (G : SimpleGraph V) (D : Finset V)
    (hD : by classical exact (G.induce (↑D : Set V)).maxDegree ≤ 1) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, G.Adj x y → G.Adj x z → y = z := by
  classical
  intro x hx y hy z hz hxy hxz
  let H := G.induce (↑D : Set V)
  let u : (↑D : Set V) := ⟨x,hx⟩
  let v : (↑D : Set V) := ⟨y,hy⟩
  let w : (↑D : Set V) := ⟨z,hz⟩
  have h := (H.degree_le_maxDegree u).trans hD
  have hv : v ∈ H.neighborFinset u := (H.mem_neighborFinset _ _).mpr hxy
  have hw : w ∈ H.neighborFinset u := (H.mem_neighborFinset _ _).mpr hxz
  exact congrArg Subtype.val (card_le_one.mp h _ hv _ hw)

private theorem indep_card_in_induce (G : SimpleGraph V) (U : Set V)
    {R : Finset V} (hRU : ∀ x ∈ R, x ∈ U) (hR : G.IsIndepSet (↑R : Set V)) :
    R.card ≤ (G.induce U).indepNum := by
  classical
  let f : R → U := fun x => ⟨x.val,hRU x.val x.property⟩
  have hf : Function.Injective f := by
    intro x y e
    have h := congrArg Subtype.val e
    exact Subtype.ext h
  let B := (univ : Finset R).image f
  have he : B.card = R.card := by
    rw [card_image_of_injective _ hf,card_univ,Fintype.card_coe]
  have hi : (G.induce U).IsIndepSet (↑B : Set U) := by
    intro x hx y hy hne hxy
    obtain ⟨a,_,rfl⟩ := mem_image.mp (show x ∈ B from hx)
    obtain ⟨b,_,rfl⟩ := mem_image.mp (show y ∈ B from hy)
    exact hR a.property b.property (fun e => hne (Subtype.ext e)) hxy
  exact he ▸ hi.card_le_indepNum

theorem two_independence_bound_any_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V) :
    by classical exact twoIndepNum G ≤ G.indepNum + (G.induce Aᶜ).indepNum +
          (G.induce A).edgeFinset.card := by
  classical
  unfold twoIndepNum
  apply Finset.sup_le_iff.mpr
  intro D hD
  have hD' := (mem_filter.mp hD).2
  have huniq := unique_adj_on_dissociation G D hD'
  let e := Fintype.equivFin V
  let rank (x : V) : ℕ := if x ∈ A then (e x).val else Fintype.card V+(e x).val
  have low (x : V) : (e x).val < Fintype.card V := (e x).isLt
  have compare {x y : V} (hx : x ∈ A) (hy : y ∉ A) : rank x < rank y := by
    dsimp [rank]
    rw [if_pos hx,if_neg hy]
    have := low x
    omega
  have inj : Function.Injective rank := by
    intro x y eq
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · exact e.injective (Fin.ext (by simpa [rank,hx,hy] using eq))
    · exact (Nat.ne_of_lt (compare hx hy) eq).elim
    · exact (Nat.ne_of_lt (compare hy hx) eq.symm).elim
    · have h : Fintype.card V+(e x).val = Fintype.card V+(e y).val := by
        simpa [rank,hx,hy] using eq
      exact e.injective (Fin.ext (by omega))
  let R := D.filter (fun x => ∃ y ∈ D, G.Adj x y ∧ rank y < rank x)
  let B := D \ R
  have hRsub : R ⊆ D := filter_subset _ _
  have hB : G.IsIndepSet (↑B : Set V) := by
    intro x hx y hy hn hxy
    obtain ⟨hxD,hxR⟩ := mem_sdiff.mp (show x ∈ B from hx)
    obtain ⟨hyD,hyR⟩ := mem_sdiff.mp (show y ∈ B from hy)
    rcases lt_or_gt_of_ne (fun eq => hn (inj eq)) with h | h
    · exact hyR (mem_filter.mpr ⟨hyD,x,hxD,hxy.symm,h⟩)
    · exact hxR (mem_filter.mpr ⟨hxD,y,hyD,hxy,h⟩)
  have hR : G.IsIndepSet (↑R : Set V) := by
    intro x hx y hy _hn hxy
    obtain ⟨hxD,u,huD,hxu,hu⟩ := mem_filter.mp (show x ∈ R from hx)
    obtain ⟨hyD,v,hvD,hyv,hv⟩ := mem_filter.mp (show y ∈ R from hy)
    have eu := huniq x hxD u huD y hyD hxu hxy
    have ev := huniq y hyD v hvD x hxD hyv hxy.symm
    rw [eu] at hu
    rw [ev] at hv
    omega
  let T := R.filter (fun x => x ∈ A)
  let U := R.filter (fun x => x ∉ A)
  have hT (x : T) : x.val ∈ A := (mem_filter.mp x.property).2
  have hinside (x : T) :
      ∃ y, y ∈ A ∧ y ∈ D ∧ G.Adj x.val y ∧ rank y < rank x.val := by
    obtain ⟨_,y,hyD,hxy,hlt⟩ := mem_filter.mp (mem_filter.mp x.property).1
    have hy : y ∈ A := by
      by_cases hy : y ∈ A
      · exact hy
      · exact (not_lt_of_ge (compare (hT x) hy).le hlt).elim
    exact ⟨y,hy,hyD,hxy,hlt⟩
  choose p hpA _hpD hpAdj hpRank using hinside
  let φ (x : T) : Sym2 A := s(⟨x.val,hT x⟩,⟨p x,hpA x⟩)
  have hφ : Function.Injective φ := by
    intro x y eq
    change s((⟨x.val,hT x⟩ : A),⟨p x,hpA x⟩) =
      s((⟨y.val,hT y⟩ : A),⟨p y,hpA y⟩) at eq
    rcases Sym2.mk_eq_mk_iff.mp eq with h | h
    · exact Subtype.ext (congrArg (fun z : A × A => z.1.val) h)
    · have hx : x.val = p y := congrArg (fun z : A × A => z.1.val) h
      have hy : p x = y.val := congrArg (fun z : A × A => z.2.val) h
      have a := hpRank x
      have b := hpRank y
      rw [hy] at a
      rw [← hx] at b
      omega
  have him : (univ.image φ) ⊆ (G.induce A).edgeFinset := by
    intro f hf
    obtain ⟨x,_,rfl⟩ := mem_image.mp hf
    exact mem_edgeFinset.mpr (show (G.induce A).Adj ⟨x.val,hT x⟩ ⟨p x,hpA x⟩ from hpAdj x)
  have hTC := card_le_card him
  rw [card_image_of_injective _ hφ, card_univ, Fintype.card_coe] at hTC
  have hUC : U.card ≤ (G.induce Aᶜ).indepNum :=
    indep_card_in_induce G Aᶜ (fun _ hx => (mem_filter.mp hx).2)
      (fun _ hx _ hy hn h => hR (filter_subset _ _ hx) (filter_subset _ _ hy) hn h)
  have hBC := hB.card_le_indepNum
  have hsplit : T.card+U.card = R.card := filter_card_add_filter_neg_card_eq_card (s := R) (fun x => x ∈ A)
  have hsplit' : B.card+R.card = D.card := card_sdiff_add_card_eq_card hRsub
  omega

noncomputable def minimumDegreeVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  {v | G.degree v = G.minDegree}

noncomputable def degreeAtMostTwoVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  {v | G.degree v ≤ 2}

theorem conjecture438a (G : SimpleGraph V) [DecidableRel G.Adj] (_hc : G.Connected)
    (_hn : 3 < Fintype.card V) :
    by
      classical
      exact twoIndepNum G ≤ G.indepNum + (G.induce (minimumDegreeVertices G)ᶜ).indepNum +
        (G.induce (minimumDegreeVertices G)).edgeFinset.card := by
  exact two_independence_bound_any_subset G (minimumDegreeVertices G)


#print axioms two_independence_bound_any_subset
#print axioms conjecture438a

end Graffiti438
