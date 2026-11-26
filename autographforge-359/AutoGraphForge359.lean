import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-! Standalone for Lean 4.19.0 and Mathlib v4.19.0. -/

namespace GraffitiPendant
open Finset SimpleGraph
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

def Pendant (x : V) : Prop := ∃! y, G.Adj x y

def Support (s : V) : Prop := ∃ l, Pendant G l ∧ G.Adj l s

def Dominates (D : Finset V) : Prop := ∀ x, x ∈ D ∨ ∃ y ∈ D, G.Adj x y

variable [Fintype V]

def outsideSupports : Finset V := univ.filter (fun x => ¬Support G x)

@[simp] theorem mem_outside {x : V} : x ∈ outsideSupports G ↔ ¬Support G x := by
  simp [outsideSupports]

/-- Connectedness rules out a component consisting of a single isolated edge. -/
theorem pendant_not_support (h : G.Connected) (hn : 2 < Fintype.card V)
    {v : V} (pv : Pendant G v) : ¬Support G v := by
  classical
  rintro ⟨l,pl,lv⟩
  have closed : ∀ x, x = v ∨ x = l := by
    intro x
    have r := (G.reachable_iff_reflTransGen v x).mp (h v x)
    induction r with
    | refl => exact Or.inl rfl
    | tail _ e ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (pv.unique e lv.symm)
      · exact Or.inl (pl.unique e lv)
  have sub : (univ : Finset V) ⊆ {v,l} := by
    intro x _
    simpa using closed x
  have bound := card_le_card sub
  have pair := card_insert_le v ({l} : Finset V)
  simp only [card_univ,card_singleton] at bound pair
  omega

end
end GraffitiPendant

/-! Ján Pastorek, AutoGraphForge normalized line 359 (raw rank 375),
ID 3078e600, commit 4d1a8afc99447cacd2328cca20e47b6493e8dbc5. -/
namespace AutoGraphForge359
open Finset SimpleGraph GraffitiPendant
variable {V : Type*} (G : SimpleGraph V)

def Restrained (D : Finset V) : Prop := Dominates G D ∧
  ∀ v ∉ D, ∃ w ∉ D, G.Adj v w

noncomputable def restrainedNumber : ℕ := sInf {k | ∃ D : Finset V, Restrained G D ∧ D.card = k}

private def cyclicNext {k : ℕ} (h : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k,Nat.mod_lt _ h⟩

/-- Every nonconstant circular sequence of truth values has a false-to-true boundary. -/
private theorem boundary {k : ℕ} (h : 0 < k) (P : Fin k → Prop)
    (off : ∃ i, ¬P i) (on' : ∃ i, P i) : ∃ i, ¬P i ∧ P (cyclicNext h i) := by
  classical
  by_contra! no
  obtain ⟨u,hu⟩ := off
  obtain ⟨v,hv⟩ := on'
  let atIndex (n : ℕ) : Fin k := ⟨(u.val+n)%k,Nat.mod_lt _ h⟩
  have all (n : ℕ) : ¬P (atIndex n) := by
    induction n with
    | zero => simpa [atIndex,Nat.mod_eq_of_lt u.isLt] using hu
    | succ n ih =>
      have eq : atIndex (n+1) = cyclicNext h (atIndex n) := by
        apply Fin.ext
        simp [atIndex,cyclicNext,Nat.mod_add_mod,Nat.add_assoc]
      rw [eq]
      exact no _ ih
  have eq : atIndex (k-u.val+v.val) = v := by
    apply Fin.ext
    change (u.val+(k-u.val+v.val))%k = v.val
    rw [show u.val+(k-u.val+v.val) = k+v.val by omega,Nat.add_mod_left,Nat.mod_eq_of_lt v.isLt]
  exact all _ (eq ▸ hv)

/-- A set dominating both a triangle-free graph and its complement gives a coloring. -/
theorem colorable_of_global_domination [Nonempty V] (tri : G.CliqueFree 3)
    {D : Finset V} (dom : Dominates G D) (compl : Dominates Gᶜ D) : G.Colorable D.card := by
  classical
  have positive : 0 < D.card := by
    let v : V := Classical.arbitrary V
    rcases dom v with hv | ⟨w,hw,_⟩
    · exact card_pos.mpr ⟨v,hv⟩
    · exact card_pos.mpr ⟨w,hw⟩
  let e := D.equivFin
  let d (i : Fin D.card) : V := (e.symm i).val
  have noTriangle {x y z : V} (xy : G.Adj x y) (xz : G.Adj x z) (yz : G.Adj y z) : False :=
    tri {x,y,z} (is3Clique_triple_iff.mpr ⟨xy,xz,yz⟩)
  have edgeColor (v : V) (out : v ∉ D) :
      ∃ i, ¬G.Adj v (d i) ∧ G.Adj v (d (cyclicNext positive i)) := by
    apply boundary positive
    · obtain ⟨b,bd,vb⟩ := (compl v).resolve_left out
      exact ⟨e ⟨b,bd⟩,by simpa [d] using ((G.compl_adj v b).mp vb).2⟩
    · obtain ⟨b,bd,vb⟩ := (dom v).resolve_left out
      exact ⟨e ⟨b,bd⟩,by simpa [d] using vb⟩
  let color (v : V) : Fin D.card := if h : v ∈ D then e ⟨v,h⟩ else (edgeColor v h).choose
  have inside (v : V) (h : v ∈ D) : d (color v) = v := by simp [d,color,h]
  have outside (v : V) (h : v ∉ D) :
      ¬G.Adj v (d (color v)) ∧ G.Adj v (d (cyclicNext positive (color v))) := by
    simpa [color,h] using (edgeColor v h).choose_spec
  refine ⟨Coloring.mk color (fun {u v} uv eq => ?_)⟩
  by_cases hu : u ∈ D <;> by_cases hv : v ∈ D
  · exact uv.ne ((inside u hu).symm.trans ((congrArg d eq).trans (inside v hv)))
  · apply (outside v hv).1
    simpa [← eq,inside u hu] using uv.symm
  · apply (outside u hu).1
    simpa [eq,inside v hv] using uv
  · apply noTriangle uv (outside u hu).2
    rw [eq]
    exact (outside v hv).2

theorem colorable_of_restrained [Nonempty V] (tri : G.CliqueFree 3)
    {D : Finset V} (rd : Restrained G D) : G.Colorable D.card := by
  classical
  apply colorable_of_global_domination G tri rd.1
  intro v
  by_cases hv : v ∈ D
  · exact Or.inl hv
  · obtain ⟨w,wo,vw⟩ := rd.2 v hv
    obtain ⟨b,bd,wb⟩ := (rd.1 w).resolve_left wo
    refine Or.inr ⟨b,bd,(G.compl_adj v b).mpr ⟨fun e => hv (e ▸ bd),fun vb => ?_⟩⟩
    exact tri {v,w,b} (is3Clique_triple_iff.mpr ⟨vw,vb,wb⟩)

theorem survivor_line359 [Fintype V] (n : 2 ≤ Fintype.card V) (tri : G.CliqueFree 3) :
    G.chromaticNumber ≤ (restrainedNumber G : ℕ∞) := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp n
  have all : Restrained G univ := ⟨fun v => Or.inl (mem_univ v),
    fun v h => (h (mem_univ v)).elim⟩
  have ex : {k | ∃ D : Finset V, Restrained G D ∧ D.card = k}.Nonempty := ⟨_,univ,all,rfl⟩
  obtain ⟨D,rd,size⟩ := Nat.sInf_mem ex
  change D.card = restrainedNumber G at size
  rw [← size]
  exact (colorable_of_restrained G tri rd).chromaticNumber_le

#print axioms colorable_of_global_domination
#print axioms colorable_of_restrained
#print axioms survivor_line359
end AutoGraphForge359
