/-
Graffiti.pc #379, also Conjecture 1 of DeLaViña, Larson, Pepper, and Waller
(2009), https://math1um.github.io/Research/r05.pdf .
For a finite tree of order greater than two, cΔ + dd/3 ≤ γₜ, where cΔ
counts components induced by the maximum-degree vertices and dd counts
distinct degrees. Reserve distinct incident edges for a total dominating
set and independent representatives of the max-degree components; the
number of unreserved edges bounds how many different degrees can occur.
Reproduce with Lean 4.19.0 / Mathlib v4.19.0 and lake env lean.
AI-assisted work for review; no priority claim.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators

namespace Graffiti379
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def TotalDom (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDomination : Nat :=
  sInf {k | ∃ D, TotalDom G D ∧ D.card = k}

def maxVertices : Finset V := Finset.univ.filter (fun v => G.degree v = G.maxDegree)

noncomputable def maxComponentCount : Nat :=
  Nat.card ((G.induce (maxVertices G : Set V)).ConnectedComponent)

def distinctDegrees : Nat := ((Finset.univ : Finset V).image (fun v => G.degree v)).card

theorem representatives : ∃ I : Finset V, I.card = maxComponentCount G ∧
    (∀ v ∈ I, G.degree v = G.maxDegree) ∧
    (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) := by
  classical
  let H := G.induce (maxVertices G : Set V)
  have hex (c : H.ConnectedComponent) : ∃ v, H.connectedComponentMk v = c := Quot.exists_rep c
  let rep (c : H.ConnectedComponent) : (maxVertices G : Set V) := Classical.choose (hex c)
  have hrep (c : H.ConnectedComponent) : H.connectedComponentMk (rep c) = c :=
    Classical.choose_spec (hex c)
  letI : Finite H.ConnectedComponent := Finite.of_surjective _ (fun c => ⟨rep c,hrep c⟩)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let f : H.ConnectedComponent → V := fun c => (rep c).1
  have inj : Function.Injective f := by
    intro a b h
    have hs : rep a = rep b := Subtype.ext h
    exact (hrep a).symm.trans ((congrArg H.connectedComponentMk hs).trans (hrep b))
  let I := Finset.univ.image f
  refine ⟨I,?_,?_,?_⟩
  · unfold I
    rw [Finset.card_image_of_injOn inj.injOn]
    simp [maxComponentCount, H, Nat.card_eq_fintype_card]
  · intro v hv
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp (rep c).property).2
  · intro u hu v hv ne edge
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hv
    have hadj : H.Adj (rep c) (rep d) := edge
    have hcd := SimpleGraph.ConnectedComponent.sound hadj.reachable
    rw [hrep c,hrep d] at hcd
    exact ne (congrArg f hcd)

theorem incident_disjoint {I : Finset V}
    (hI : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) :
    Set.PairwiseDisjoint (↑I : Set V) (fun v : V => G.incidenceFinset v) := by
  intro u hu v hv ne
  apply Finset.disjoint_left.mpr
  intro e hue hve
  have h1 := (G.mem_incidenceFinset u e).mp hue
  have h2 := (G.mem_incidenceFinset v e).mp hve
  exact hI u hu v hv ne (SimpleGraph.adj_iff_exists_edge.mpr ⟨ne,e,h1.1,h1.2,h2.2⟩)

theorem independentDegree (I : Finset V)
    (hI : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v)
    (hmax : ∀ v ∈ I, G.degree v = G.maxDegree) :
    I.card * G.maxDegree ≤ G.edgeFinset.card := by
  have hx := Finset.card_biUnion (incident_disjoint G hI)
  rw [Finset.sum_const_nat (fun v hv =>
    (G.card_incidenceFinset_eq_degree v).trans (hmax v hv))] at hx
  rw [← hx]
  apply Finset.card_le_card
  intro e he
  obtain ⟨u,_,he⟩ := Finset.mem_biUnion.mp he
  exact SimpleGraph.mem_edgeFinset.mpr ((G.mem_incidenceFinset u e).mp he).1

theorem dominatingDegree (D : Finset V) (hD : TotalDom G D) :
    Fintype.card V ≤ D.card * G.maxDegree := by
  have hc : (Finset.univ : Finset V) ⊆ D.biUnion (fun w => G.neighborFinset w) := by
    intro v _
    obtain ⟨w,hw,e⟩ := hD v
    exact Finset.mem_biUnion.mpr ⟨w,hw,(G.mem_neighborFinset w v).mpr e.symm⟩
  calc
    Fintype.card V ≤ (D.biUnion (fun w => G.neighborFinset w)).card := by
      simpa using Finset.card_le_card hc
    _ ≤ ∑ w ∈ D, (G.neighborFinset w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ D, G.maxDegree := by
      apply Finset.sum_le_sum
      intro w _
      rw [G.card_neighborFinset_eq_degree]
      exact G.degree_le_maxDegree w
    _ = D.card * G.maxDegree := Finset.sum_const_nat (fun _ _ => rfl)

theorem minDomExists (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    ∃ D : Finset V, TotalDom G D ∧ D.card = totalDomination G := by
  classical
  have hd : TotalDom G Finset.univ := by
    intro v
    obtain ⟨w,hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := hT.isConnected v w
    cases p with
    | nil => exact False.elim (hne rfl)
    | @cons _ u _ he _ => exact ⟨u,Finset.mem_univ _,he⟩
  have ha : ({k : Nat | ∃ D : Finset V, TotalDom G D ∧ D.card = k}).Nonempty :=
    ⟨_,_,hd,rfl⟩
  exact Nat.sInf_mem ha

/-- One edge is reserved for each vertex outside D and for each independent
representative inside D. These edge choices are mutually distinct. -/
theorem residualBound (hT : G.IsTree) (I D : Finset V) (hD : TotalDom G D)
    (hI : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v)
    (hmax : ∀ v ∈ I, G.degree v = G.maxDegree) :
    ((I \ D).card * (G.maxDegree-1) ≤ D.card - (I∩D).card - 1) ∧
    ∀ v, v ∉ D → G.degree v ≤ D.card - (I∩D).card := by
  classical
  let OUT := (Finset.univ : Finset V) \ D
  let IN := I ∩ D
  let X := OUT ∪ IN
  let f (v : V) : V := Classical.choose (hD v)
  have fD (v : V) : f v ∈ D := (Classical.choose_spec (hD v)).1
  have fAdj (v : V) : G.Adj v (f v) := (Classical.choose_spec (hD v)).2
  let chooseEdge (v : V) : Sym2 V := s(v,f v)
  let reserved := X.image chooseEdge
  have hinD (u : V) (hu : u ∈ X) (h : u ∈ D) : u ∈ I := by
    rcases Finset.mem_union.mp hu with ho | hi
    · exact False.elim ((Finset.mem_sdiff.mp ho).2 h)
    · exact (Finset.mem_inter.mp hi).1
  have inj : Set.InjOn chooseEdge (↑X : Set V) := by
    intro u hu v hv h
    change u ∈ X at hu
    change v ∈ X at hv
    change s(u,f u) = s(v,f v) at h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.1
    · have uD : u ∈ D := h.1.symm ▸ fD v
      have vD : v ∈ D := h.2 ▸ fD u
      have e : G.Adj u v := h.2 ▸ fAdj u
      exact False.elim (hI u (hinD u hu uD) v (hinD v hv vD) e.ne e)
  have reserveSub : reserved ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr (fAdj u))
  have hdisjoint : Disjoint OUT IN := by
    apply Finset.disjoint_left.mpr
    intro u h₁ h₂
    exact (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).2
  have hX : X.card = (Fintype.card V - D.card) + IN.card := by
    rw [Finset.card_union_of_disjoint hdisjoint]
    have h := Finset.card_sdiff (Finset.subset_univ D)
    simpa [OUT] using congrArg (fun a : Nat => a + IN.card) h
  have hrr : reserved.card = X.card := Finset.card_image_of_injOn inj
  let R := G.edgeFinset \ reserved
  have hR := Finset.card_sdiff_add_card_eq_card reserveSub
  change R.card + reserved.card = G.edgeFinset.card at hR
  have hTree := hT.card_edgeFinset
  have hDc : D.card ≤ Fintype.card V := Finset.card_le_univ D
  have hin : IN.card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
  have hRc : R.card + 1 + IN.card = D.card := by omega
  let rest (u : V) := (G.incidenceFinset u).erase (chooseEdge u)
  have restSub (u : V) (hu : u ∉ D) : rest u ⊆ R := by
    intro e he
    have ino := Finset.mem_erase.mp he
    have inc := (G.mem_incidenceFinset u e).mp ino.2
    apply Finset.mem_sdiff.mpr
    refine ⟨SimpleGraph.mem_edgeFinset.mpr inc.1,?_⟩
    intro h
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp h
    rw [← hv] at inc
    have e' : u ∈ s(v,f v) := inc.2
    rcases Sym2.mem_iff.mp e' with eq | eq
    · subst u
      exact ino.1 hv.symm
    · exact hu (eq.symm ▸ fD v)
  have restCard (u : V) : (rest u).card = G.degree u - 1 := by
    have ce : chooseEdge u ∈ G.incidenceFinset u :=
      (G.mem_incidenceFinset u _).mpr ((G.mem_incidenceSet u (f u)).mpr (fAdj u))
    rw [Finset.card_erase_of_mem ce,G.card_incidenceFinset_eq_degree]
  have hDis : Set.PairwiseDisjoint (↑(I \ D) : Set V) rest := by
    intro u hu v hv hne
    change u ∈ I \ D at hu
    change v ∈ I \ D at hv
    have hn := incident_disjoint G hI
    have hdis := hn (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1 hne
    exact hdis.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hcount : ((I \ D).biUnion rest).card = (I \ D).card * (G.maxDegree-1) := by
    rw [Finset.card_biUnion hDis]
    apply Finset.sum_const_nat
    intro u hu
    rw [restCard,hmax u (Finset.mem_sdiff.mp hu).1]
  have hsub : ((I \ D).biUnion rest) ⊆ R := by
    intro e he
    obtain ⟨u,hu,hue⟩ := Finset.mem_biUnion.mp he
    exact restSub u (Finset.mem_sdiff.mp hu).2 hue
  have hlo := Finset.card_le_card hsub
  rw [hcount] at hlo
  constructor
  · change (I \ D).card * (G.maxDegree-1) ≤ D.card-IN.card-1
    omega
  · intro u hu
    have deg := Finset.card_le_card (restSub u hu)
    rw [restCard] at deg
    change G.degree u ≤ D.card - IN.card
    omega

private theorem degree_pos (hT : G.IsTree) (hn : 2 < Fintype.card V) (v : V) :
    0 < G.degree v := by
  obtain ⟨D,hD,_⟩ := minDomExists G hT hn
  obtain ⟨w,_,hw⟩ := hD v
  have h := Finset.card_pos.mpr ⟨w,(G.mem_neighborFinset v w).mpr hw⟩
  simpa [G.card_neighborFinset_eq_degree] using h


theorem bound379 (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : TotalDom G D) :
    3*maxComponentCount G + distinctDegrees G ≤ 3*D.card := by
  classical
  obtain ⟨I, hIc, hDeg, hI⟩ := representatives G
  let k := I.card
  let t := D.card
  let d := G.maxDegree
  let δ := t-k
  have he := hT.card_edgeFinset
  have h1 : k*d ≤ G.edgeFinset.card := independentDegree G I hI hDeg
  have h2 : Fintype.card V ≤ t*d := dominatingDegree G D hD
  have hkt : k < t := by
    by_cases hb : t ≤ k
    · have hh := Nat.mul_le_mul_right d hb
      omega
    · omega
  have hδpos : 1 ≤ δ := by dsimp [δ]; omega
  have ht : t = k+δ := by dsimp [δ]; omega
  have hPos : ∀ u, 0 < G.degree u := degree_pos G hT hn
  have degreeRange (b : Nat) : ((Finset.range (b+1)).erase 0).card = b := by
    have hm : 0 ∈ Finset.range (b+1) := by simp
    rw [Finset.card_erase_of_mem hm,Finset.card_range]
    omega
  have memRange (b : Nat) (v : V) (h : G.degree v ≤ b) :
      G.degree v ∈ (Finset.range (b+1)).erase 0 := by
    apply Finset.mem_erase.mpr
    exact ⟨Nat.ne_of_gt (hPos v),Finset.mem_range.mpr (by omega)⟩
  have endProof (h : distinctDegrees G ≤ 3*δ) :
      3*maxComponentCount G + distinctDegrees G ≤ 3*D.card := by
    change 3*maxComponentCount G + distinctDegrees G ≤ 3*t
    have hk : k = maxComponentCount G := hIc
    omega
  apply endProof
  by_cases easy : d ≤ 3*δ
  · let A := (Finset.range (3*δ+1)).erase 0
    have hd : ((Finset.univ : Finset V).image (fun v => G.degree v)) ⊆ A := by
      intro e he
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
      exact memRange _ _ (Nat.le_trans (G.degree_le_maxDegree v) easy)
    have hb := Finset.card_le_card hd
    rw [degreeRange] at hb
    exact hb
  · obtain ⟨hx,hOutside⟩ := residualBound G hT I D hD hI hDeg
    let j := (I \ D).card
    let q := (I ∩ D).card
    have hsplit : q+j=k := Finset.card_inter_add_card_sdiff I D
    change j*(d-1) ≤ t-q-1 at hx
    have hj : j = 0 := by
      by_cases hn : 1 ≤ j
      · have Δ2 : d-1 = (d-2)+1 := by omega
        have low := Nat.mul_le_mul_left (d-2) hn
        rw [Nat.mul_one] at low
        rw [Δ2,Nat.mul_add,Nat.mul_one,Nat.mul_comm j (d-2)] at hx
        omega
      · omega
    have hq : q=k := by omega
    have hDCard : (D \ I).card = δ := by
      have hcard := Finset.card_inter_add_card_sdiff D I
      rw [Finset.inter_comm D I] at hcard
      change q + (D \ I).card = t at hcard
      omega
    let A := (Finset.range (δ+1)).erase 0
    let B := insert d ((D \ I).image (fun v => G.degree v))
    have hsub : ((Finset.univ : Finset V).image (fun v => G.degree v)) ⊆ A∪B := by
      intro e he
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp he
      by_cases hu : u ∈ D
      · apply Finset.mem_union.mpr
        right
        by_cases hi : u ∈ I
        · apply Finset.mem_insert.mpr
          exact Or.inl (hDeg u hi)
        · apply Finset.mem_insert.mpr
          exact Or.inr (Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨hu,hi⟩,rfl⟩)
      · apply Finset.mem_union.mpr
        left
        have hout := hOutside u hu
        change G.degree u ≤ t-q at hout
        exact memRange δ u (by omega)
    have aC : A.card=δ := degreeRange δ
    have bC : B.card ≤ δ+1 := by
      calc
        B.card ≤ ((D \ I).image (fun v => G.degree v)).card+1 :=
          Finset.card_insert_le d _
        _ ≤ (D \ I).card+1 := Nat.add_le_add_right Finset.card_image_le _
        _ = δ+1 := by rw [hDCard]
    have hu := Finset.card_union_le A B
    have hd := Finset.card_le_card hsub
    change distinctDegrees G ≤ (A∪B).card at hd
    omega

/-- Graffiti.pc #379, with the denominator 3 cleared. -/
theorem conjecture379 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    3*maxComponentCount G + distinctDegrees G ≤ 3*totalDomination G := by
  obtain ⟨D,hD,he⟩ := minDomExists G hT hn
  rw [← he]
  exact bound379 G hT hn D hD

#print axioms conjecture379
end Graffiti379
