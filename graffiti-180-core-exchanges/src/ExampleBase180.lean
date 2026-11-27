import CoreSplit180
set_option warningAsError true
set_option compiler.extract_closed false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
namespace Minimal180.Case12
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
abbrev V := Fin 12
noncomputable def oldEdges : List (V×V) := [(0,6),(1,7),(2,7),(1,8),(3,8),(0,9),(4,9),(5,9),(2,10),(4,10),(6,10),(3,11),(5,11),(6,11),(10,11)]
noncomputable def graph (E:List (V×V)) : SimpleGraph V where
  Adj a b := a≠b ∧ ((a,b)∈E ∨ (b,a)∈E)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl
noncomputable instance (E) : DecidableRel (graph E).Adj := fun a b => inferInstanceAs (Decidable (a≠b ∧ ((a,b)∈E ∨ (b,a)∈E)))
noncomputable abbrev G := graph ((7,8)::oldEdges)
noncomputable abbrev J := graph oldEdges
noncomputable abbrev A : Finset V := {0,1,2,3,4,5}
noncomputable abbrev P : Finset V := {0,4,5,7,8,10,11}
noncomputable abbrev U : Finset V := {0,1,2,3,4,5,7,8,10,11}
noncomputable abbrev C : Finset V := {0,1,2,5,7}
noncomputable abbrev L : Finset V := {0,1,3,5,11}
noncomputable def d (i j:V) : ℕ := (([[0,5,3,3,2,2,1,4,4,1,2,2],[5,0,2,2,4,4,4,1,1,5,3,3],[3,2,0,3,2,3,2,1,2,3,1,2],[3,2,3,0,3,2,2,2,1,3,2,1],[2,4,2,3,0,2,2,3,4,1,1,2],[2,4,3,2,2,0,2,4,3,1,2,1],[1,4,2,2,2,2,0,3,3,2,1,1],[4,1,1,2,3,4,3,0,1,4,2,3],[4,1,2,1,4,3,3,1,0,4,3,2],[1,5,3,3,1,1,2,4,4,0,2,2],[2,3,1,2,1,2,1,2,3,2,0,1],[2,3,2,1,2,1,1,3,2,2,1,0]]:List (List ℕ))[j.val]!)[i.val]!
theorem dist_data (r:V) : G.Connected ∧ ∀ i,G.dist i r=d i r := by
  apply layers
  · exact (show ∀ j,d j j=0 by decide) r
  · intro i j; exact (show ∀ k a b,G.Adj a b → d a k≤d b k+1 by decide) r i j
  · exact (show ∀ k a,a≠k → ∃ b,G.Adj a b ∧ d a k=d b k+1 by decide) r
theorem jc : J.Connected := by
  apply (layers J 0 (fun i => d i 0) (by decide) _ _).1
  · intro i j; exact (show ∀ a b,J.Adj a b → d a 0≤d b 0+1 by decide) i j
  · decide
private noncomputable def avoidD (c i:V) : ℕ := (([[88,0,2,2,4,4,4,1,1,5,3,3],[3,88,0,3,2,3,2,1,2,3,1,2],[3,2,88,0,3,2,2,2,1,3,2,1],[2,4,2,88,0,2,2,3,4,1,1,2],[2,4,3,2,88,0,2,4,3,1,2,1],[1,4,2,2,2,88,0,3,3,2,1,1],[5,1,1,2,3,4,88,0,1,4,2,3],[4,1,4,1,4,3,3,88,0,4,3,2],[1,5,3,3,1,1,2,4,88,0,2,2],[2,3,1,2,1,2,1,2,3,88,0,1],[2,3,4,1,3,1,1,3,2,2,88,0],[0,5,3,6,2,2,1,4,5,1,2,88]]:List (List ℕ))[c.val]!)[i.val]!
theorem block : NoCut G := by apply noCut_of_routes G (fun c=>c+1) avoidD <;> decide
theorem add_eq : J⊔SimpleGraph.edge 7 8=G := by
  ext a b
  change (J.Adj a b ∨ (SimpleGraph.edge 7 8).Adj a b) ↔ _
  rw [edge_adj]
  exact (show ∀ i j : V,(J.Adj i j ∨ ((i=7 ∧ j=8 ∨ i=8 ∧ j=7) ∧ i≠j)) ↔ G.Adj i j by decide) a b

theorem con {H : SimpleGraph V} {S : Finset V} (r:V) (depth:V→ℕ) (hr:r∈S)
    (down : ∀ v∈S,v≠r → ∃ b∈S,H.Adj v b ∧ depth b<depth v) : Con H S := by
  apply (connected_cuts _ _).mpr
  refine ⟨⟨r,hr⟩,?_⟩
  intro f ok
  have same (v:V) (h:v∈S) : f v=f r := by
    induction k : depth v using Nat.strong_induction_on generalizing v with
    | h k ih =>
      by_cases vr : v=r
      · rw [vr]
      · obtain ⟨b,hb,vb,lt⟩ := down v h vr
        exact (ok v h b hb vb).trans (ih _ (k ▸ lt) b hb rfl)
  exact fun a ha b hb => (same a ha).trans (same b hb).symm

noncomputable def single (z:V) : Finset V := insert z (C.erase 7)
private noncomputable def cut (z i : V) : Bool := ((if z=3 then 3664 else if z=4 then 3528 else if z=10 then 2504 else if z=11 then 392 else 0):ℕ).testBit i.val

theorem specified_exchange :
    NeedsTip J C (univ\C) 7 8 ∧
    (∀ z∈(U\C).erase 8, ¬Con G (univ\single z)) ∧
    L⊆U\{7,8} ∧ L.card=C.card ∧ (L\C).card=2 ∧ (C\L).card=2 ∧
    Con G (univ\L) ∧ (∀ q∈L, Dominates G (univ\L) q) ∧ ¬Con J (univ\L) := by
  have tip : NeedsTip J C (univ\C) 7 8 := by
    refine ⟨by decide,by decide,con 3 (fun i => [88,88,88,0,3,88,2,88,1,4,2,1][i.val]!) (by decide) (by decide),?_,?_⟩
    all_goals unfold Dominates; decide
  have no (z:V) (hz:z∈(U\C).erase 8) : ¬Con G (univ\single z) := by
    intro connected
    have all : ∀ t∈(U\C).erase 8, OnEdges G (univ\single t) (cut t) ∧ ¬ConstantOn (univ\single t) (cut t) := by
      unfold OnEdges ConstantOn; decide
    obtain ⟨kept,bad⟩ := all z hz
    exact bad (((connected_cuts _ _).mp connected).2 _ kept)
  refine ⟨tip,no,by decide,by decide,by decide,by decide,
    con 2 (fun i => [88,88,0,88,2,88,2,1,2,3,1,88][i.val]!) (by decide) (by decide),?_,?_⟩
  · unfold Dominates; decide
  · intro connected
    let f (i:V) := decide (i=8)
    have kept : OnEdges J (univ\L) f := by dsimp only [OnEdges,f]; decide
    have bad : ¬ConstantOn (univ\L) f := by dsimp only [ConstantOn,f]; decide
    exact bad (((connected_cuts _ _).mp connected).2 _ kept)

#print axioms specified_exchange
end Minimal180.Case12
