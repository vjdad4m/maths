import Packing
import HallRainbow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases

namespace CubicRainbow791
open Finset SimpleGraph Graffiti326 AutoGraphForge378 TriangleMatching1078 HallRainbow1121
abbrev V := Fin 20
def n0 : V → V := ![8,8,9,12,12,13,14,15,0,0,1,1,3,3,4,4,5,5,0,6]
def n1 : V → V := ![9,10,10,13,14,16,16,17,1,2,2,2,4,5,6,7,6,7,3,7]
def n2 : V → V := ![18,11,11,18,15,17,19,19,9,8,11,10,13,12,15,14,17,16,19,18]

def relation (u v : V) := v=n0 u ∨ v=n1 u ∨ v=n2 u
def g : SimpleGraph V where
  Adj := relation
  symm := by unfold Symmetric relation; decide
  loopless := by unfold Irreflexive relation; decide
instance : DecidableRel g.Adj := fun u v => by
  change Decidable (v=n0 u ∨ v=n1 u ∨ v=n2 u)
  infer_instance

theorem cubic : g.IsRegularOfDegree 3 := by
  intro v
  fin_cases v <;> decide

theorem connected : g.Connected := by
  have h0 : g.Reachable 0 0 := .rfl
  have h8 : g.Reachable 0 8 := h0.trans ((by decide : g.Adj 0 8).reachable)
  have h9 : g.Reachable 0 9 := h0.trans ((by decide : g.Adj 0 9).reachable)
  have h18 : g.Reachable 0 18 := h0.trans ((by decide : g.Adj 0 18).reachable)
  have h1 : g.Reachable 0 1 := h8.trans ((by decide : g.Adj 8 1).reachable)
  have h2 : g.Reachable 0 2 := h9.trans ((by decide : g.Adj 9 2).reachable)
  have h3 : g.Reachable 0 3 := h18.trans ((by decide : g.Adj 18 3).reachable)
  have h19 : g.Reachable 0 19 := h18.trans ((by decide : g.Adj 18 19).reachable)
  have h10 : g.Reachable 0 10 := h1.trans ((by decide : g.Adj 1 10).reachable)
  have h11 : g.Reachable 0 11 := h1.trans ((by decide : g.Adj 1 11).reachable)
  have h12 : g.Reachable 0 12 := h3.trans ((by decide : g.Adj 3 12).reachable)
  have h13 : g.Reachable 0 13 := h3.trans ((by decide : g.Adj 3 13).reachable)
  have h6 : g.Reachable 0 6 := h19.trans ((by decide : g.Adj 19 6).reachable)
  have h7 : g.Reachable 0 7 := h19.trans ((by decide : g.Adj 19 7).reachable)
  have h4 : g.Reachable 0 4 := h12.trans ((by decide : g.Adj 12 4).reachable)
  have h5 : g.Reachable 0 5 := h13.trans ((by decide : g.Adj 13 5).reachable)
  have h14 : g.Reachable 0 14 := h6.trans ((by decide : g.Adj 6 14).reachable)
  have h16 : g.Reachable 0 16 := h6.trans ((by decide : g.Adj 6 16).reachable)
  have h15 : g.Reachable 0 15 := h7.trans ((by decide : g.Adj 7 15).reachable)
  have h17 : g.Reachable 0 17 := h7.trans ((by decide : g.Adj 7 17).reachable)
  have all (v : V) : g.Reachable 0 v := by fin_cases v <;> assumption
  exact ⟨fun x y => (all x).symm.trans (all y)⟩

def tip (i : Fin 6) (b : Bool) : V :=
  ⟨8+2*i.val+(if b then 1 else 0),by have := i.isLt; split <;> omega⟩

theorem match_exact : lineDomination g = 6 ∧ minMaximalMatching g = 6 := by
  let f : Fin 6 × Bool ↪ V := ⟨fun p => tip p.1 p.2,by unfold Function.Injective; decide⟩
  have edges : ∀ i, g.Adj (f (i,false)) (f (i,true)) := by decide
  have maxM : HasMaximalMatching g 6 := ⟨f,edges,by decide⟩
  let designated (i : Fin 6) : g.edgeSet := ⟨s(f (i,false),f (i,true)),edges i⟩
  have distinct : ∀ i j : Fin 6, ∀ b c : Bool, i ≠ j → ¬g.Adj (f (i,b)) (f (j,c)) := by decide
  have apart (e : g.edgeSet) (i j : Fin 6)
      (hi : ∃ v, v ∈ e.val ∧ v ∈ (designated i).val)
      (hj : ∃ w, w ∈ e.val ∧ w ∈ (designated j).val) : i=j := by
    obtain ⟨v,ve,vi⟩ := hi
    obtain ⟨w,we,wj⟩ := hj
    obtain ⟨b,rfl⟩ : ∃ b : Bool, v=f (i,b) :=
      (Sym2.mem_iff.mp vi).elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
    obtain ⟨c,rfl⟩ : ∃ c : Bool, w=f (j,c) :=
      (Sym2.mem_iff.mp wj).elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
    apply Classical.byContradiction
    intro ne
    have neq : f (i,b) ≠ f (j,c) := fun eq => ne (congrArg Prod.fst (f.injective eq))
    exact distinct i j b c ne (show s(f (i,b),f (j,c)) ∈ g.edgeSet from
      ((Sym2.mem_and_mem_iff neq).mp ⟨ve,we⟩) ▸ e.property)
  have lo : 6 ≤ lineDomination g := by simpa using packing_lower g designated apart
  have mid := lineDomination_le_matching g
  have hi : minMaximalMatching g ≤ 6 := Nat.sInf_le maxM
  omega

end CubicRainbow791
