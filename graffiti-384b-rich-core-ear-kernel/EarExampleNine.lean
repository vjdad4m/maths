import EarFootprint
namespace Graffiti384b.OddStars.EarExampleNine
open Finset SimpleGraph EarPacking EarFootprint
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
def N : Fin 9 → Finset (Fin 9)
  | 0 => {2,4,5,6,8}
  | 1 => {3,4,5}
  | 2 => {0,4,5}
  | 3 => {1,5}
  | 4 => {0,1,2,5,7}
  | 5 => {0,1,2,3,4,6,7}
  | 6 => {0,5}
  | 7 => {4,5}
  | 8 => {0}
def graph : SimpleGraph (Fin 9) where
  Adj u v := v∈N u
  symm := by have h : ∀u v : Fin 9,v∈N u → u∈N v := by decide
             exact fun _ _ e => h _ _ e
  loopless := by have h : ∀v : Fin 9,v∉N v := by decide
                 exact h
instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v∈N u))
def F : Finset (Fin 9) := {6,7}
theorem profile : List.ofFn (trianglesAt graph)=[4,2,3,1,5,7,1,1,0] ∧
    graph.degree 8=1 ∧ bound graph=5 ∧ anchors graph F={0,4,5} ∧
    residual graph F={1,2} ∧ ¬graph.Adj 1 2 ∧ ¬graph.Adj 6 7 := by decide
theorem supported_core : ∀u v : Fin 9,u≠8 → v≠8 → graph.Adj u v →
    ∃w : Fin 9,w≠8 ∧ graph.Adj u w ∧ graph.Adj v w := by decide

theorem connected : graph.Connected := by
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨5,fun v => ?_⟩
  have hub : ∀v : Fin 9,v=5 ∨ graph.Adj 5 v ∨ (graph.Adj 5 0 ∧ graph.Adj 0 v) := by decide
  rcases hub v with rfl|a|⟨a,b⟩
  · exact Reachable.refl _
  · exact a.reachable
  · exact a.reachable.trans b.reachable

theorem tight : gamma graph=5 := by
  let D : Finset (Fin 9) := {0,1,4,5,8}
  have dom : TwoDominates graph D := (by decide : ∀v : Fin 9,v∉({0,1,4,5,8}:Finset (Fin 9)) → 2≤nbr graph v {0,1,4,5,8})
  have sz : D.card=5 := by decide
  have att : ∃d,TwoDominates graph d ∧ d.card=5 := ⟨D,dom,sz⟩
  apply le_antisymm (Nat.sInf_le att)
  apply le_csInf ⟨5,att⟩
  rintro k ⟨d,dk,rfl⟩
  have clause (v : Fin 9) (b : Finset (Fin 9)) (cap : (N v\b).card≤1) :
      v∈d ∨ ∃w∈b,w∈d := by
    by_contra! miss
    have low := dk v miss.1
    have sub : d.filter (graph.Adj v)⊆N v\b := fun w wm => mem_sdiff.mpr
      ⟨(mem_filter.mp wm).2,fun wb => miss.2 w wb (mem_filter.mp wm).1⟩
    have hi := (card_le_card sub).trans cap
    change 2≤(d.filter (graph.Adj v)).card at low
    omega
  have leaf := clause 8 ∅ (by decide)
  simp only [not_mem_empty,false_and,exists_false,or_false] at leaf
  have ea := clause 3 {1} (by decide)
  have eb := clause 6 {0} (by decide)
  have ec := clause 7 {4} (by decide)
  simp only [mem_singleton,exists_eq_left] at ea eb ec
  by_cases hub : (5:Fin 9)∈d
  · obtain ⟨a,am,ad⟩ : ∃a∈({1,3}:Finset (Fin 9)),a∈d := ea.elim (fun m => ⟨3,by decide,m⟩) (fun m => ⟨1,by decide,m⟩)
    obtain ⟨b,bm,bd⟩ : ∃b∈({0,6}:Finset (Fin 9)),b∈d := eb.elim (fun m => ⟨6,by decide,m⟩) (fun m => ⟨0,by decide,m⟩)
    obtain ⟨c,cm,cd⟩ : ∃c∈({4,7}:Finset (Fin 9)),c∈d := ec.elim (fun m => ⟨7,by decide,m⟩) (fun m => ⟨4,by decide,m⟩)
    have sizes : ∀a∈({1,3}:Finset (Fin 9)),∀b∈({0,6}:Finset (Fin 9)),∀c∈({4,7}:Finset (Fin 9)),({8,5,a,b,c}:Finset (Fin 9)).card=5 := by decide
    rw [←sizes a am b bm c cm]
    exact card_le_card (insert_subset leaf (insert_subset hub (insert_subset ad (insert_subset bd (singleton_subset_iff.mpr cd)))))
  · have ears (v : Fin 9) (c : (N v\{5}).card≤1) : v∈d := by
      have h := clause v {5} c
      simpa only [mem_singleton,exists_eq_left,or_iff_left hub] using h
    have extra := clause 2 {0,4} (by decide)
    obtain ⟨a,am,ad⟩ : ∃a∈({0,2,4}:Finset (Fin 9)),a∈d := extra.elim
      (fun m => ⟨2,by decide,m⟩) (fun ⟨w,wm,m⟩ => ⟨w,(show ({0,4}:Finset (Fin 9))⊆{0,2,4} by decide) wm,m⟩)
    have sizes : ∀a∈({0,2,4}:Finset (Fin 9)),({8,3,6,7,a}:Finset (Fin 9)).card=5 := by decide
    rw [←sizes a am]
    exact card_le_card (insert_subset leaf (insert_subset (ears 3 (by decide)) (insert_subset (ears 6 (by decide)) (insert_subset (ears 7 (by decide)) (singleton_subset_iff.mpr ad)))))
end Graffiti384b.OddStars.EarExampleNine
#print axioms Graffiti384b.OddStars.EarExampleNine.profile
#print axioms Graffiti384b.OddStars.EarExampleNine.supported_core
#print axioms Graffiti384b.OddStars.EarExampleNine.connected
#print axioms Graffiti384b.OddStars.EarExampleNine.tight
