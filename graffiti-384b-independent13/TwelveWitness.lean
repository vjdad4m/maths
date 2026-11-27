import IndependentThirteen
namespace Graffiti384b.Simplicial16.Example
open Finset SimpleGraph
private def mask (v : Fin 33) : Nat := #[62,1019799805,1537622779,1425981687,1073498863,515031263,190,532554110,247767168,6729761812,2316454400,531817490,57344,126638466,238992446,530995498,917504,465423532,535552412,531062938,522341560,463391420,58982682,493791678,385788564,494857652,60615098,314494390,197036734,18,12,1536,512][v.val]!
def graph : SimpleGraph (Fin 33) where
  Adj v w := (mask v).testBit w.val=true
  symm := by
    have z : ∀ v w : Fin 33,(mask v).testBit w.val=true → (mask w).testBit v.val=true := by decide
    exact fun i j => z i j
  loopless := by change ∀ v : Fin 33,¬(mask v).testBit v.val=true; decide
instance : DecidableRel graph.Adj := fun v w => inferInstanceAs (Decidable ((mask v).testBit w.val=true))

private def score (v : Fin 33) : Nat := #[10,79,88,95,124,92,15,113,26,11,16,71,2,41,91,75,3,100,107,82,67,111,18,112,86,115,81,103,109,1,1,1,0][v.val]!
private def degree (v : Fin 33) : Nat := #[5,18,18,19,22,17,6,19,9,8,8,15,3,12,18,16,3,18,19,16,14,18,8,19,17,20,16,18,18,2,2,2,1][v.val]!
private def parent (v : Fin 33) : Fin 33 := #[0,0,0,0,0,0,1,1,7,2,11,1,13,1,1,1,19,2,2,1,3,2,1,1,2,2,1,1,1,1,2,9,9][v.val]!
private def depth (v : Fin 33) : Nat := #[0,1,1,1,1,1,2,2,3,2,3,2,3,2,2,2,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3][v.val]!

set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

private theorem degrees : ∀ v,graph.degree v=degree v := by decide
private def row (v : Fin 33) : List (Fin 33) :=
  #[[1,2,3,4,5],
    [0,2,3,4,5,6,7,11,13,14,15,19,22,23,26,27,28,29],
    [0,1,3,4,5,6,7,9,14,17,18,21,23,24,25,27,28,30],
    [0,1,2,4,5,6,7,14,15,17,18,19,20,21,22,23,26,28,30],
    [0,1,2,3,5,6,7,9,11,14,18,19,20,21,22,23,24,25,26,27,28,29],
    [0,1,2,3,4,6,7,14,15,17,20,21,23,25,26,27,28],
    [1,2,3,4,5,7],
    [1,2,3,4,5,6,8,13,17,18,19,20,21,23,24,25,26,27,28],
    [7,13,15,18,22,23,25,26,27],
    [2,4,10,21,24,28,31,32],
    [9,11,14,17,20,25,27,31],
    [1,4,10,13,14,15,17,20,21,23,24,25,26,27,28],
    [13,14,15],
    [1,7,8,11,12,14,18,19,23,24,25,26],
    [1,2,3,4,5,10,11,12,13,15,17,18,19,20,21,25,26,27],
    [1,3,5,8,11,12,14,17,18,21,23,24,25,26,27,28],
    [17,18,19],
    [2,3,5,7,10,11,14,15,16,18,19,20,21,23,24,25,27,28],
    [2,3,4,7,8,13,14,15,16,17,19,21,22,23,24,25,26,27,28],
    [1,3,4,7,13,14,16,17,18,21,23,24,25,26,27,28],
    [3,4,5,7,10,11,14,17,21,24,25,26,27,28],
    [2,3,4,5,7,9,11,14,15,17,18,19,20,23,24,25,27,28],
    [1,3,4,8,18,23,24,25],
    [1,2,3,4,5,7,8,11,13,15,17,18,19,21,22,24,26,27,28],
    [2,4,7,9,11,13,15,17,18,19,20,21,22,23,25,26,28],
    [2,4,5,7,8,10,11,13,14,15,17,18,19,20,21,22,24,26,27,28],
    [1,3,4,5,7,8,11,13,14,15,18,19,20,23,24,25],
    [1,2,4,5,7,8,10,11,14,15,17,18,19,20,21,23,25,28],
    [1,2,3,4,5,7,9,11,15,17,18,19,20,21,23,24,25,27],
    [1,4],
    [2,3],
    [9,10],
    [9]][v.val]!

private def linkCount : List (Fin 33) → Nat
  | [] => 0
  | z::zs => linkCount zs+(zs.filter (fun w => decide (graph.Adj z w))).length

private theorem links (l : List (Fin 33)) (nd : l.Nodup) :
    (HighEar.pairs graph l.toFinset).card=linkCount l := by
  induction l with
  | nil => decide
  | cons z zs ih =>
    obtain ⟨off,rest⟩ := List.nodup_cons.mp nd
    rw [List.toFinset_cons,HighEar.pairs_insert graph (by simpa using off),ih rest]
    congr 1
    have eq : zs.toFinset.filter (graph.Adj z)=(zs.filter (fun w => decide (graph.Adj z w))).toFinset := by ext w; simp
    exact (congrArg card eq).trans (List.toFinset_card_of_nodup (rest.filter _))

private theorem scores : ∀ v,trianglesAt graph v=score v := by
  have actual : ∀ v,graph.neighborFinset v=(row v).toFinset := by decide
  have nd : ∀ v,(row v).Nodup := by decide
  have counts : ∀ v,linkCount (row v)=score v := by decide
  intro v
  change (HighEar.pairs graph (graph.neighborFinset v)).card=_
  rw [actual,links _ (nd v),counts]

theorem connected : graph.Connected := by
  have up : ∀ v : Fin 33,v≠0 → graph.Adj (parent v) v ∧ depth (parent v)<depth v := by decide
  have path (n : ℕ) : ∀ v,depth v=n → graph.Reachable 0 v := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v eq
      by_cases zero : v=0
      · subst v; exact Reachable.rfl
      obtain ⟨edge,lt⟩ := up v zero
      exact (ih _ (eq ▸ lt) _ rfl).trans edge.reachable
  exact ⟨fun u v => (path _ u rfl).symm.trans (path _ v rfl)⟩


/-- A realized twelve-contact profile with both anchor score bounds attained. -/
theorem profile : (types graph).card=31 ∧ (nonleaves graph).card=32 ∧ (high graph).card=29 ∧
    LowSample.twos graph={29,30,31} ∧ graph.neighborFinset 29={1,4} ∧
    graph.neighborFinset 30={2,3} ∧ graph.neighborFinset 31={9,10} ∧
    graph.neighborFinset 9∩graph.neighborFinset 10={31} ∧ graph.neighborFinset 32={9} ∧
    ((({31,9,10}:Finset (Fin 33))ᶜ).filter (fun v => 0<nbr graph v {9,10})).card=12 ∧
    nbr graph 9 (high graph \ {9,10})=5 ∧ nbr graph 10 (high graph \ {9,10})=6 ∧
    trianglesAt graph 9=11 ∧ trianglesAt graph 10=16 ∧ gamma graph≤11 ∧ bound graph=17 := by
  have t : (types graph).card=31 := by rw [types,funext scores]; decide
  refine ⟨t,?_,?_,?_,by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,?_,?_,?_,?_⟩
  · unfold nonleaves; simp only [degrees]; decide
  · unfold high; simp only [degrees]; decide
  · unfold LowSample.twos nonleaves high; simp only [degrees]; decide
  · unfold high; simp only [degrees]; decide
  · unfold high; simp only [degrees]; decide
  · rw [scores]; decide
  · rw [scores]; decide
  · let S : Finset (Fin 33) := {32,9,10,15,1,2,14,17,3,18,4}
    have dom : TwoDominates graph S := by unfold TwoDominates; decide
    have size : S.card=11 := by decide
    exact Nat.sInf_le ⟨S,dom,size⟩
  · rw [bound,t]; decide

end Graffiti384b.Simplicial16.Example
#print axioms Graffiti384b.Simplicial16.Example.connected
#print axioms Graffiti384b.Simplicial16.Example.profile

