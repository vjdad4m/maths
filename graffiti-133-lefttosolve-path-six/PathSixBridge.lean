import HexFlattened133
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

namespace OMA133Port
open SimpleGraph Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

def inducedList (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ ∀ i j : Fin p.length, G.Adj (p.get i) (p.get j) ↔
    i.val+1=j.val ∨ j.val+1=i.val

theorem inducedList_ofFn (G : SimpleGraph V) {n : ℕ} (f : Fin n→V)
    (hf : Graffiti133.InducedPath G f) : inducedList G (List.ofFn f) := by
  refine ⟨List.nodup_ofFn.mpr hf.1,?_⟩
  intro i j
  have hi : i.val<n := by simpa using i.isLt
  have hj : j.val<n := by simpa using j.isLt
  let a : Fin n := ⟨i.val,hi⟩
  let b : Fin n := ⟨j.val,hj⟩
  have ha : (List.ofFn f).get i=f a := by simp [a,List.get_eq_getElem]
  have hb : (List.ofFn f).get j=f b := by simp [b,List.get_eq_getElem]
  rw [ha,hb]
  rcases lt_trichotomy a b with ab|same|ba
  · rw [hf.2 _ _ ab]
    have ab' : i.val < j.val := ab
    change i.val+1=j.val ↔ _
    omega
  · have eq : i.val=j.val := congrArg (fun t : Fin n => t.val) same
    rw [same]
    simp [show i.val+1≠j.val by omega,show j.val+1≠i.val by omega]
  · rw [SimpleGraph.adj_comm,hf.2 _ _ ba]
    have ba' : j.val < i.val := ba
    change j.val+1=i.val ↔ _
    omega

theorem neighborhood_indepNum_eq (G : SimpleGraph V) (v : V) :
    (G.induce (G.neighborSet v)).indepNum = Graffiti133.localIndependence G v := by
  classical
  let H := G.induce (G.neighborSet v)
  have setMem (T : Finset V) : T∈Graffiti133.localIndependentSets G v ↔
      (∀ x∈T,G.Adj v x) ∧ ∀ x∈T,∀ y∈T,¬ G.Adj x y := by
    simp only [Graffiti133.localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_iff, Finset.mem_univ, true_and]
  apply le_antisymm
  · obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
    let T := s.map (Function.Embedding.subtype _)
    have Tm : T ∈ Graffiti133.localIndependentSets G v := (setMem T).mpr (by
      constructor
      · intro x hx
        obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
        exact y.2
      · intro x hx y hy ad
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
        have ane : a≠b := fun eq=>ad.ne (congrArg Subtype.val eq)
        exact hs.isIndepSet ha hb ane ad)
    have tl : T.card ≤ Graffiti133.localIndependence G v := Finset.le_sup (f := Finset.card) Tm
    rwa [Finset.card_map, hs.card_eq] at tl
  · apply Finset.sup_le_iff.mpr
    intro T Tm
    obtain ⟨tb,ti⟩ := (setMem T).mp Tm
    let U : Finset (G.neighborSet v) := T.subtype (fun x=>x∈G.neighborSet v)
    have eq : U.card=T.card := by
      rw [Finset.card_subtype]
      congr 1
      exact Finset.filter_true_of_mem (fun x hx=>tb x hx)
    rw [←eq]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro a ha b hb _
    exact ti _ (Finset.mem_subtype.mp ha) _ (Finset.mem_subtype.mp hb)

noncomputable def meanReal (G : SimpleGraph V) : ℝ :=
  (∑ v, ((G.induce (G.neighborSet v)).indepNum : ℝ))/Fintype.card V

theorem meanReal_eq (G : SimpleGraph V) : meanReal G=(Graffiti133.averageLocal G : ℝ) := by
  unfold meanReal Graffiti133.averageLocal
  have hs := map_sum (Rat.castHom ℝ)
    (fun v : V => (Graffiti133.localIndependence G v : ℚ)) (Finset.univ : Finset V)
  simp only [Rat.castHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at hs
  rw [Rat.cast_div, hs, Rat.cast_natCast]
  simp only [neighborhood_indepNum_eq, Rat.cast_natCast]

theorem radius_three_path_six_bound (G : SimpleGraph V) (hc : G.Connected)
    (h4 : ¬ ∃ a b c d : V, a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    (path : ℕ) (pathUpper : ∀ p : List V, inducedList G p→p.length≤path) (hp : path=6) :
    meanReal G≤3 := by
  by_contra hh
  have ha : 3 < Graffiti133.averageLocal G := by
    have hreal : (3:ℝ) < (Graffiti133.averageLocal G : ℝ) := by
      rw [← meanReal_eq]
      exact lt_of_not_ge hh
    exact_mod_cast hreal
  obtain ⟨f,hf⟩ := Graffiti133Revisit.P7_of_strict_mean_three G hc ((Graffiti133.fourCycleFree_iff G).mpr h4) ha
  have hl := pathUpper (List.ofFn f) (inducedList_ofFn G f hf)
  simp [hp] at hl

#print axioms radius_three_path_six_bound
end OMA133Port
