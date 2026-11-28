import Witness
import Row595

namespace CubicBridges1160
open SimpleGraph Finset Graffiti326

private def charge : Vertex → Vertex → Unit ⊕ Fin 3
  | some (i,_), some _ => .inr i
  | _, _ => .inl ()

theorem matching_cap {k : ℕ} (hm : HasMatching graph k) : k ≤ 10 := by
  classical
  obtain ⟨f,hf⟩ := hm
  let c (i : Fin k) := charge (f (i,false)) (f (i,true))
  let fiber (z : Unit ⊕ Fin 3) := {i : Fin k // c i = z}
  have count : k = ∑ z, Fintype.card (fiber z) := by
    simpa [fiber,Fintype.card_sigma] using (Fintype.card_congr (Equiv.sigmaFiberEquiv c)).symm
  have hubCap (h : Unit) : Fintype.card (fiber (.inl h)) ≤ 1 := by
    have hit (i : fiber (.inl h)) : ∃ b, f (i.val,b) = none := by
      have e := i.property
      change charge (f (i.val,false)) (f (i.val,true)) = .inl h at e
      cases ha : f (i.val,false) with
      | none => exact ⟨false,ha⟩
      | some a =>
        cases hb : f (i.val,true) with
        | none => exact ⟨true,hb⟩
        | some b =>
          rw [ha,hb] at e
          rcases a with ⟨j,u⟩
          cases e
    have hs : Subsingleton (fiber (.inl h)) := ⟨by
      intro i j
      obtain ⟨a,ea⟩ := hit i
      obtain ⟨b,eb⟩ := hit j
      exact Subtype.ext (Prod.mk.inj (f.injective (ea.trans eb.symm))).1⟩
    exact Fintype.card_le_one_iff_subsingleton.mpr hs
  have blockCap (p : Fin 3) : Fintype.card (fiber (.inr p)) ≤ 3 := by
    have hit (z : fiber (.inr p) × Bool) : ∃ j, f (z.1.val,z.2) = some (p,j) := by
      rcases z with ⟨i,b⟩
      have e := i.property
      change charge (f (i.val,false)) (f (i.val,true)) = .inr p at e
      have a := hf i.val
      cases h₀ : f (i.val,false) with
      | none => rw [h₀] at e; cases e
      | some x =>
        cases h₁ : f (i.val,true) with
        | none =>
          rw [h₀,h₁] at e
          rcases x with ⟨j,u⟩
          cases e
        | some y =>
          rcases x with ⟨j,u⟩
          rcases y with ⟨l,v⟩
          rw [h₀,h₁] at e a
          have jp : j = p := Sum.inr.inj e
          have jl : j = l := a.1
          subst j
          subst l
          cases b
          · exact ⟨u,h₀⟩
          · exact ⟨v,h₁⟩
    let port (z : fiber (.inr p) × Bool) := (hit z).choose
    have inj : Function.Injective port := by
      rintro ⟨i,a⟩ ⟨j,b⟩ he
      have ep := congrArg (fun v : Fin 7 => (some (p,v) : Vertex)) he
      have e := f.injective (((hit (i,a)).choose_spec.trans ep).trans (hit (j,b)).choose_spec.symm)
      exact Prod.ext (Subtype.ext (Prod.mk.inj e).1) (Prod.mk.inj e).2
    have small := Fintype.card_le_of_injective port inj
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at small
    omega
  rw [count,Fintype.sum_sum_type]
  have left := sum_le_sum (s := (univ : Finset Unit)) (fun h _ => hubCap h)
  have right := sum_le_sum (s := (univ : Finset (Fin 3))) (fun p _ => blockCap p)
  simp only [sum_const,card_univ,Fintype.card_unit,Fintype.card_fin,smul_eq_mul] at left right
  omega

private def matchingEnds : Fin 10 → Bool → Vertex
  | 0, false => none
  | 0, true => some (0,0)
  | 1, false => some (0,1)
  | 1, true => some (0,5)
  | 2, false => some (0,2)
  | 2, true => some (0,6)
  | 3, false => some (0,3)
  | 3, true => some (0,4)
  | 4, false => some (1,1)
  | 4, true => some (1,5)
  | 5, false => some (1,2)
  | 5, true => some (1,6)
  | 6, false => some (1,3)
  | 6, true => some (1,4)
  | 7, false => some (2,1)
  | 7, true => some (2,5)
  | 8, false => some (2,2)
  | 8, true => some (2,6)
  | 9, false => some (2,3)
  | 9, true => some (2,4)

theorem matching_exact : matchingNumber graph = 10 := by
  apply le_antisymm (matching_cap (matchingNumber_attained _))
  apply matchingNumber_upper
  have inj : ∀ a b : Fin 10 × Bool, matchingEnds a.1 a.2 = matchingEnds b.1 b.2 →
    a = b := by decide
  have adj : ∀ i, graph.Adj (matchingEnds i false) (matchingEnds i true) := by decide
  exact ⟨⟨fun p => matchingEnds p.1 p.2,inj⟩,adj⟩

def Covers {V : Type*} (G : SimpleGraph V) (P : Finset G.edgeSet) :=
  ∀ v : V, ∃ e ∈ P, v ∈ e.val

noncomputable def edgeCoverNumber {V : Type*} (G : SimpleGraph V) :=
  sInf {k : ℕ | ∃ P : Finset G.edgeSet, P.card=k ∧ Covers G P}

theorem cliqueCover_le_cover_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    {P : Finset G.edgeSet} (hp : Covers G P) : cliqueCover G ≤ P.card := by
  classical
  choose e he hv using hp
  let f (v : V) : ↥P := ⟨e v,he v⟩
  let c : Gᶜ.Coloring ↥P := Coloring.mk f (by
    intro a b hab eq
    have same : (e a).val = (e b).val := congrArg (fun x : ↥P => x.val.val) eq
    have ha := hv a
    have hb := hv b
    rw [← same] at hb
    have notAdj := ((G.compl_adj a b).mp hab).2
    have ne := ((G.compl_adj a b).mp hab).1
    obtain ⟨⟨u,v⟩,hrep⟩ := Quot.exists_rep (e a).val
    change s(u,v) = (e a).val at hrep
    rw [← hrep] at ha hb
    have hadj : G.Adj u v := by
      change s(u,v) ∈ G.edgeSet
      rw [hrep]
      exact (e a).property
    rcases Sym2.mem_iff.mp ha with rfl|rfl <;> rcases Sym2.mem_iff.mp hb with rfl|rfl
    · exact ne rfl
    · exact notAdj hadj
    · exact notAdj hadj.symm
    · exact ne rfl)
  apply Nat.sInf_le
  simpa using c.colorable

private def coverEnds (i : Fin 12) (b : Bool) : Vertex :=
  if h : i.val < 10 then matchingEnds ⟨i.val,h⟩ b
  else if b then some (if i.val = 10 then 1 else 2,0) else none

theorem edge_cover_exact : edgeCoverNumber graph = 12 := by
  classical
  have isEdge : ∀ i : Fin 12, graph.Adj (coverEnds i false) (coverEnds i true) := by decide
  let edge (i : Fin 12) : graph.edgeSet := ⟨s(coverEnds i false,coverEnds i true),isEdge i⟩
  let P := univ.image edge
  have allCovered : ∀ v : Vertex, ∃ i : Fin 12, v = coverEnds i false ∨ v = coverEnds i true := by decide
  have hp : Covers graph P := by
    intro v
    obtain ⟨i,hi⟩ := allCovered v
    exact ⟨edge i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,Sym2.mem_iff.mpr hi⟩
  have ub := Nat.sInf_le (s := {k | ∃ P : Finset graph.edgeSet, P.card=k ∧ Covers graph P})
    (show P.card ∈ _ from ⟨P,rfl,hp⟩)
  have size : P.card ≤ 12 := card_image_le.trans (by simp)
  apply le_antisymm (ub.trans size)
  obtain ⟨Q,hq,hcov⟩ := Nat.sInf_mem (s := {k | ∃ P : Finset graph.edgeSet,
    P.card=k ∧ Covers graph P}) ⟨_,P,rfl,hp⟩
  have lb := cliqueCover_le_cover_card graph hcov
  rwa [cover_exact,hq] at lb

theorem harmonic_exact : RegularHarmonic595.harmonicIndex graph = 11 := by
  rw [RegularHarmonic595.harmonic_regular graph (by decide : 0 < 3) cubic, order]
  norm_num

theorem size_exact : graph.edgeFinset.card = 33 := by decide

theorem counterexample :
    1 < Fintype.card Vertex ∧ graph.IsRegularOfDegree 3 ∧ TriangleFree graph ∧ graph.Connected ∧
    annihilation graph = 11 ∧ edgeCoverNumber graph = 12 ∧ matchingNumber graph = 10 ∧
    RegularHarmonic595.harmonicIndex graph = 11 ∧ cliqueCover graph = 12 ∧
    Fintype.card Vertex = 22 ∧ graph.edgeFinset.card = 33 :=
  ⟨by rw [order]; decide,cubic,no_triangle,connected,annihilation_exact,edge_cover_exact,
    matching_exact,harmonic_exact,cover_exact,order,size_exact⟩

-- Concrete failures of the pinned catalogue inequalities; the graph class
-- hypotheses are certified together in `counterexample`.
theorem row837 : annihilation graph ≠ edgeCoverNumber graph := by
  rw [annihilation_exact,edge_cover_exact]; decide
theorem row838 : edgeCoverNumber graph ≠ matchingNumber graph := by
  rw [edge_cover_exact,matching_exact]; decide
theorem row839 : annihilation graph ≠ matchingNumber graph := by
  rw [annihilation_exact,matching_exact]; decide
theorem row840 : RegularHarmonic595.harmonicIndex graph ≠ (matchingNumber graph : ℚ) := by
  rw [harmonic_exact,matching_exact]; decide
theorem row841 : (edgeCoverNumber graph : ℚ) ≠ RegularHarmonic595.harmonicIndex graph := by
  rw [edge_cover_exact,harmonic_exact]; decide
theorem row843 : ¬ (cliqueCover graph : ℚ) ≤ RegularHarmonic595.harmonicIndex graph := by
  rw [cover_exact,harmonic_exact]; decide
theorem row844 : 2 * edgeCoverNumber graph ≠ Fintype.card Vertex := by
  rw [edge_cover_exact,order]; decide
theorem row845 : 2 * matchingNumber graph ≠ Fintype.card Vertex := by
  rw [matching_exact,order]; decide
theorem row846 : 3 * matchingNumber graph ≠ graph.edgeFinset.card := by
  rw [matching_exact,size_exact]; decide
theorem row847 : 3 * edgeCoverNumber graph ≠ graph.edgeFinset.card := by
  rw [edge_cover_exact,size_exact]; decide

theorem row832 : ¬ cliqueCover graph ≤ matchingNumber graph := by
  rw [cover_exact,matching_exact]; decide
theorem row848 : (1/2 : ℚ) * Fintype.card Vertex ≠ (edgeCoverNumber graph : ℚ) := by
  rw [order,edge_cover_exact]; norm_num
theorem row849 : (1/2 : ℚ) * Fintype.card Vertex ≠ (matchingNumber graph : ℚ) := by
  rw [order,matching_exact]; norm_num
theorem row850 : (1/3 : ℚ) * graph.edgeFinset.card ≠ (matchingNumber graph : ℚ) := by
  rw [size_exact,matching_exact]; norm_num
theorem row851 : (1/3 : ℚ) * graph.edgeFinset.card ≠ (edgeCoverNumber graph : ℚ) := by
  rw [size_exact,edge_cover_exact]; norm_num
theorem row1161 : ¬ 2 * cliqueCover graph ≤ Fintype.card Vertex := by
  rw [cover_exact,order]; decide
theorem row1162 : ¬ 3 * cliqueCover graph ≤ graph.edgeFinset.card := by
  rw [cover_exact,size_exact]; decide

#print axioms counterexample
#print axioms row832
#print axioms row848
#print axioms row849
#print axioms row850
#print axioms row851
#print axioms row1161
#print axioms row1162
#print axioms row837
#print axioms row838
#print axioms row839
#print axioms row840
#print axioms row841
#print axioms row843
#print axioms row844
#print axioms row845
#print axioms row846
#print axioms row847
end CubicBridges1160
