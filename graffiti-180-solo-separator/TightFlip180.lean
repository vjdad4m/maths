import TightPrime180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 600000
namespace Minimal180.PairRepair.Tight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals

private theorem thrice {a b c d : Bool} (h : a≠b) (k : b≠c) (l : c≠d) : a≠d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem cp : ProperOn G (univ\({0,7}:Finset V)) paint := by unfold ProperOn;decide

theorem no_fixed_monochrome (c : V→Bool) (ok : ProperOn G (univ\({0,7}:Finset V)) c) :
    c 1≠c 2 ∧ c 3≠c 8 := ⟨thrice (ok 1 (by decide) 5 (by decide) (by decide))
      (ok 5 (by decide) 6 (by decide) (by decide)) (ok 6 (by decide) 2 (by decide) (by decide)),
      ok 3 (by decide) 8 (by decide) (by decide)⟩

private theorem rule (S : Finset V) (sr : S⊆univ\({0,7}:Finset V)) (z : V) (t : Bool) :
    TerminalColor G 0 7 (S.erase z) t ↔ RelativeCheck G (S.erase z) 0 7 paint t := by
  have inc := (erase_subset z S).trans sr
  have a : (0:V)∉S.erase z := fun m => (mem_sdiff.mp (inc m)).2 (by decide)
  have b : (7:V)∉S.erase z := fun m => (mem_sdiff.mp (inc m)).2 (by decide)
  exact terminal_iff_contacts G 0 7 (by decide) (by decide) _ a b paint
    (fun x xm y ym => cp x (inc xm) y (inc ym)) t

theorem masks (t : Bool) : (DropCheck G 0 7 A C paint t ↔ t=false) ∧ DropCheck G 0 7 A D paint t := by
  have csub : C⊆univ\({0,7}:Finset V) := by decide
  have dsub : D⊆univ\({0,7}:Finset V) := by decide
  constructor
  · constructor
    · rintro ⟨x,xc,xk,h⟩
      obtain ⟨e,ok,ea,eb⟩ := (rule C csub x t).mpr h
      obtain ⟨u,um,v,vm,au,uv,vb⟩ := (show ∀ x∈C,x∉A → ∃ u∈C.erase x,∃ v∈C.erase x,
        G.Adj 0 u ∧ G.Adj u v ∧ G.Adj v 7 by decide) x xc xk
      have ne := thrice (ok 0 (by simp) u (mem_union_right _ um) au) (ok u (mem_union_right _ um) v (mem_union_right _ vm) uv)
        (ok v (mem_union_right _ vm) 7 (by simp) vb)
      cases t <;> simp_all
    · rintro rfl
      let e (v : V) := decide (v∈({0,1,2}:Finset V))
      exact ⟨5,by decide,by decide,(rule C csub 5 false).mp ⟨e,by unfold ProperOn;decide,by decide,by decide⟩⟩
  · refine ⟨8,by decide,by decide,(rule D dsub 8 t).mp ?_⟩
    cases t
    · let e (v : V) := decide (v∈({0,3}:Finset V))
      exact ⟨e,by unfold ProperOn;decide,by decide,by decide⟩
    · let e (v : V) := decide (v∈({0,7}:Finset V))
      exact ⟨e,by unfold ProperOn;decide,by decide,by decide⟩

/-- The other tip has mixed contacts in both old components. The first
component forces opposite terminal colors; the second, after deletion of
8, permits both. Their common sign certifies the actual tight marking. -/
theorem tight_regression : Prime G ∧ G.Connected ∧ (∀ v,¬DomEdge G 1 v) ∧
    G.degree 0=4 ∧ allowance G 1 false A=2 ∧ Protected G 1 false A := by
  have deg := (card_neighborFinset_eq_degree G 0).symm.trans (by decide : (G.neighborFinset 0).card=4)
  have same (F H : Fintype (G.neighborSet 0)) : @SimpleGraph.degree V G 0 F=@SimpleGraph.degree V G 0 H := by
    rw [Subsingleton.elim F H]
  have degree_any (F : Fintype (G.neighborSet 0)) : @SimpleGraph.degree V G 0 F=4 := (same F _).trans deg
  have parts : TwoRegions G 0 7 C D ∅ := ⟨by decide,by decide,by decide,by decide,by decide,by decide⟩
  have left : MixedAt G 0 C paint := ⟨5,6,by decide,by decide,by decide,by decide,
    joined_step G C (joined_self G C (by decide : (5:V)∈C)) (by decide) (by decide)⟩
  have right : MixedAt G 0 D paint := ⟨8,4,by decide,by decide,by decide,by decide,
    joined_step G D (joined_self G D (by decide : (8:V)∈D)) (by decide) (by decide)⟩
  have pm : (0:V)∈parity G 1 false := by rw [data.2.1];decide
  refine ⟨prime,data.1,by unfold DomEdge;decide,deg,budget,?_⟩
  apply (active_contacts_iff G data.1 (by decide) 1 false A data.2.2.1 0 7 (by decide) (by decide)
    ((color_function ..).mpr ⟨paint,cp⟩) (by decide) pm (degree_any _) budget C D ∅ parts paint cp left right).mpr
  rw [data.2.1,data.2.2.2.2]
  exact ⟨false,(masks false).1.mpr rfl,(masks false).2⟩

#print axioms no_fixed_monochrome
#print axioms masks
#print axioms tight_regression
end Minimal180.PairRepair.Tight
