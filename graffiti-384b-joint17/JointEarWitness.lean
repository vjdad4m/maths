import RankRepair29
namespace Graffiti384b.Joint17.Example
open Finset SimpleGraph
private def mask (v : Fin 33) : Nat := #[62,1019800317,1267090171,1425982711,1054625007,515031775,190,532554110,247768192,2416839718,2389705496,4793213458,57344,126638466,104771646,530995498,917504,297650860,535552924,531063450,388123832,463391912,58983706,493791678,385788036,360506804,60616122,279743926,197036730,18,12,1536,2048][v.val]!
def graph : SimpleGraph (Fin 33) where
  Adj v w := (mask v).testBit w.val=true
  symm := by
    have z : ∀ v w : Fin 33,(mask v).testBit w.val=true → (mask w).testBit v.val=true := by decide
    exact fun i j => z i j
  loopless := by change ∀ v : Fin 33,¬(mask v).testBit v.val=true; decide
instance : DecidableRel graph.Adj := fun v w => inferInstanceAs (Decidable ((mask v).testBit w.val=true))

private def score (v : Fin 33) : Nat := #[10,81,60,97,95,88,15,105,29,19,22,45,2,39,62,69,3,73,103,80,53,79,21,107,66,77,83,56,92,1,1,1,0][v.val]!
private def degree (v : Fin 33) : Nat := #[5,19,16,20,20,18,6,19,10,10,11,14,3,12,15,16,3,16,20,17,13,16,9,19,15,17,17,14,17,2,2,2,1][v.val]!
private def parent (v : Fin 33) : Fin 33 := #[0,0,0,0,0,0,1,1,7,1,3,1,13,1,1,1,19,2,2,1,3,3,1,1,2,2,1,1,1,1,2,9,11][v.val]!
private def depth (v : Fin 33) : Nat := #[0,1,1,1,1,1,2,2,3,2,2,2,3,2,2,2,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3][v.val]!

set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

private theorem degrees : ∀ v,graph.degree v=degree v := by decide
private def row (v : Fin 33) : List (Fin 33) :=
  #[[1,2,3,4,5],
    [0,2,3,4,5,6,7,9,11,13,14,15,19,22,23,26,27,28,29],
    [0,1,3,4,5,6,7,9,14,17,18,23,24,25,27,30],
    [0,1,2,4,5,6,7,10,14,15,17,18,19,20,21,22,23,26,28,30],
    [0,1,2,3,5,6,7,10,11,14,18,19,20,22,23,25,26,27,28,29],
    [0,1,2,3,4,6,7,9,14,15,17,20,21,23,25,26,27,28],
    [1,2,3,4,5,7],
    [1,2,3,4,5,6,8,13,17,18,19,20,21,23,24,25,26,27,28],
    [7,10,13,15,18,22,23,25,26,27],
    [1,2,5,10,11,17,18,19,28,31],
    [3,4,8,9,20,21,22,25,26,27,31],
    [1,4,9,13,15,17,20,21,23,24,26,27,28,32],
    [13,14,15],
    [1,7,8,11,12,14,18,19,23,24,25,26],
    [1,2,3,4,5,12,13,15,17,18,19,20,21,25,26],
    [1,3,5,8,11,12,14,17,18,21,23,24,25,26,27,28],
    [17,18,19],
    [2,3,5,7,9,11,14,15,16,18,19,20,21,23,24,28],
    [2,3,4,7,8,9,13,14,15,16,17,19,21,22,23,24,25,26,27,28],
    [1,3,4,7,9,13,14,16,17,18,21,23,24,25,26,27,28],
    [3,4,5,7,10,11,14,17,21,24,25,26,28],
    [3,5,7,10,11,14,15,17,18,19,20,23,24,25,27,28],
    [1,3,4,8,10,18,23,24,25],
    [1,2,3,4,5,7,8,11,13,15,17,18,19,21,22,24,26,27,28],
    [2,7,11,13,15,17,18,19,20,21,22,23,25,26,28],
    [2,4,5,7,8,10,13,14,15,18,19,20,21,22,24,26,28],
    [1,3,4,5,7,8,10,11,13,14,15,18,19,20,23,24,25],
    [1,2,4,5,7,8,10,11,15,18,19,21,23,28],
    [1,3,4,5,7,9,11,15,17,18,19,20,21,23,24,25,27],
    [1,4],
    [2,3],
    [9,10],
    [11]][v.val]!

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


/-- The numerical and local hypotheses with seventeen contacts and six
different ear neighbors occur in a connected graph satisfying the bound. -/
theorem profile : (types graph).card=31 ∧ (nonleaves graph).card=32 ∧ (high graph).card=29 ∧
    LowSample.twos graph={29,30,31} ∧ graph.neighborFinset 29={1,4} ∧
    graph.neighborFinset 30={2,3} ∧ graph.neighborFinset 31={9,10} ∧
    graph.neighborFinset 9∩graph.neighborFinset 10={31} ∧
    ((({31,9,10}:Finset (Fin 33))ᶜ).filter (fun v => 0<nbr graph v {9,10})).card=17 ∧
    Frontier31.DenseCenter graph 0 ∧ Frontier31.DenseCenter graph 6 ∧ gamma graph≤11 ∧ bound graph=17 := by
  have t : (types graph).card=31 := by rw [types,funext scores]; decide
  have dc₀ : Frontier31.DenseCenter graph 0 := ⟨by rw [degrees]; decide,by rw [degrees]; decide,by rw [scores,degrees]; decide,{0,1,2,3,4},by decide,by decide⟩
  have dc₆ : Frontier31.DenseCenter graph 6 := ⟨by rw [degrees]; decide,by rw [degrees]; decide,by rw [scores,degrees]; decide,{6,1,2,3,4},by decide,by decide⟩
  refine ⟨t,?_,?_,?_,by decide,by decide,by decide,by decide,by decide,dc₀,dc₆,?_,?_⟩
  · unfold nonleaves; simp only [degrees]; decide
  · unfold high; simp only [degrees]; decide
  · unfold LowSample.twos nonleaves high; simp only [degrees]; decide
  · let S : Finset (Fin 33) := {1,2,3,4,9,10,14,15,18,19,32}
    have dom : TwoDominates graph S := by unfold TwoDominates; decide
    have size : S.card=11 := by decide
    exact Nat.sInf_le ⟨S,dom,size⟩
  · rw [bound,t]; decide

end Graffiti384b.Joint17.Example
#print axioms Graffiti384b.Joint17.Example.connected
#print axioms Graffiti384b.Joint17.Example.profile
