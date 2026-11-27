import CoreSplit180
set_option warningAsError true
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
namespace Minimal180.Case14
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
abbrev V := Fin 14
noncomputable def oldEdges : List (V×V) := [(0,1),(0,2),(0,13),(1,2),(1,3),(3,5),(4,5),(4,6),(6,7),(6,8),(7,8),(7,12),(9,10),(9,11),(9,12),(10,11),(10,13)]
noncomputable def graph (E:List (V×V)) : SimpleGraph V where
  Adj a b := a≠b ∧ ((a,b)∈E ∨ (b,a)∈E)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl
noncomputable instance (E) : DecidableRel (graph E).Adj := fun a b => inferInstanceAs (Decidable (a≠b ∧ ((a,b)∈E ∨ (b,a)∈E)))
noncomputable abbrev G := graph ((3,4)::oldEdges)
noncomputable abbrev J := graph oldEdges
noncomputable abbrev A : Finset V := {1,5,6,11,12,13}
noncomputable abbrev P : Finset V := {0,3,4,7,9,10}
noncomputable abbrev U : Finset V := {0,1,3,4,5,6,7,9,10,12,13}
noncomputable abbrev F : Finset V := {0,5,13}
noncomputable def d (i j:V) : ℕ := (([[0,1,1,2,3,3,4,5,5,3,2,3,4,1],[1,0,1,1,2,2,3,4,4,4,3,4,5,2],[1,1,0,2,3,3,4,5,5,4,3,4,5,2],[2,1,2,0,1,1,2,3,3,5,4,5,4,3],[3,2,3,1,0,1,1,2,2,4,5,5,3,4],[3,2,3,1,1,0,2,3,3,5,5,6,4,4],[4,3,4,2,1,2,0,1,1,3,4,4,2,5],[5,4,5,3,2,3,1,0,1,2,3,3,1,4],[5,4,5,3,2,3,1,1,0,3,4,4,2,5],[3,4,4,5,4,5,3,2,3,0,1,1,1,2],[2,3,3,4,5,5,4,3,4,1,0,1,2,1],[3,4,4,5,5,6,4,3,4,1,1,0,2,2],[4,5,5,4,3,4,2,1,2,1,2,2,0,3],[1,2,2,3,4,4,5,4,5,2,1,2,3,0]]:List (List ℕ))[j.val]!)[i.val]!
theorem dist_data (r:V) : G.Connected ∧ ∀ i,G.dist i r=d i r := by
  apply layers
  · exact (show ∀ j,d j j=0 by decide) r
  · intro i j; exact (show ∀ k a b,G.Adj a b → d a k≤d b k+1 by decide) r i j
  · exact (show ∀ k a,a≠k → ∃ b,G.Adj a b ∧ d a k=d b k+1 by decide) r
theorem jc : J.Connected := by
  apply (layers J 11 (fun i => d i 11) (by decide) _ _).1
  · intro i j; exact (show ∀ a b,J.Adj a b → d a 11≤d b 11+1 by decide) i j
  · decide
private noncomputable def avoidD (c i:V) : ℕ := (([[88,0,1,1,2,2,3,4,4,6,7,7,5,8],[1,88,0,9,8,9,7,6,7,4,3,4,5,2],[2,1,88,0,1,1,2,3,3,5,4,5,4,3],[7,8,8,88,0,1,1,2,2,4,5,5,3,6],[3,2,3,1,88,0,9,8,9,6,5,6,7,4],[4,3,4,2,1,88,0,1,1,3,4,4,2,5],[5,6,6,7,8,8,88,0,1,2,3,3,1,4],[5,4,5,3,2,3,1,88,0,8,7,8,9,6],[3,4,4,5,4,5,3,2,88,0,1,1,1,2],[2,3,3,4,5,5,6,7,7,88,0,1,8,1],[8,7,8,6,5,6,4,3,4,1,88,0,2,9],[4,5,5,4,3,4,2,1,2,1,2,88,0,3],[1,2,2,3,4,4,5,6,6,2,1,2,88,0],[0,1,1,2,3,3,4,5,5,7,8,8,6,88]]:List (List ℕ))[c.val]!)[i.val]!
theorem block : NoCut G := by apply noCut_of_routes G (fun c=>c+1) avoidD <;> decide
theorem add_eq : J⊔SimpleGraph.edge 3 4=G := by
  ext a b
  change (J.Adj a b ∨ (SimpleGraph.edge 3 4).Adj a b) ↔ _
  rw [edge_adj]
  exact (show ∀ i j : V,(J.Adj i j ∨ ((i=3 ∧ j=4 ∨ i=4 ∧ j=3) ∧ i≠j)) ↔ G.Adj i j by decide) a b

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

noncomputable abbrev C3 : Finset V := {1,3,5}
private noncomputable def cut3 (z i:V) : Bool := ((if z=0 then 4 else if z=6 then 16261 else if z=7 then 15877 else if z=9 then 11269 else if z=10 then 8197 else if z=12 then 11781 else if z=13 then 5 else 0):ℕ).testBit i.val
theorem tip3 : NeedsTip J C3 (univ\C3) 3 4 := by
  refine ⟨by decide,by decide,con 0 (fun i => [0,88,1,88,7,88,6,5,6,3,2,3,4,1][i.val]!) (by decide) (by decide),?_,?_⟩
  all_goals unfold Dominates; decide
theorem forced3 (K : Finset V) (sz:K.card=3) (tip:NeedsTip J K (univ\K) 3 4) : K=C3 := by
  have sub : C3⊆K := by
    intro a ha
    rcases (show ∀ i∈C3,i=3 ∨ J.Adj 3 i by decide) a ha with eq|edge
    · exact eq ▸ tip.1
    · by_contra outside
      exact tip.2.2.2.1 ⟨a,mem_sdiff.mpr ⟨mem_univ _,outside⟩,edge⟩
  exact (eq_of_subset_of_card_le sub (by rw [sz]; decide)).symm
theorem stuck3 (z:V) (hz:z∈(U\C3).erase 4) :
    ¬Con G (univ\insert z (C3.erase 3)) := by
  intro connected
  have all : ∀ t∈(U\C3).erase 4,OnEdges G (univ\insert t (C3.erase 3)) (cut3 t) ∧
      ¬ConstantOn (univ\insert t (C3.erase 3)) (cut3 t) := by unfold OnEdges ConstantOn; decide
  obtain ⟨h,n⟩ := all z hz
  exact n (((connected_cuts _ _).mp connected).2 _ h)
noncomputable abbrev C4 : Finset V := {4,5,6}
private noncomputable def cut4 (z i:V) : Bool := ((if z=0 then 30 else if z=1 then 16261 else if z=7 then 15903 else if z=9 then 11295 else if z=10 then 8223 else if z=12 then 11807 else if z=13 then 31 else 0):ℕ).testBit i.val
theorem tip4 : NeedsTip J C4 (univ\C4) 4 3 := by
  refine ⟨by decide,by decide,con 0 (fun i => [0,1,1,2,88,88,88,5,6,3,2,3,4,1][i.val]!) (by decide) (by decide),?_,?_⟩
  all_goals unfold Dominates; decide
theorem forced4 (K : Finset V) (sz:K.card=3) (tip:NeedsTip J K (univ\K) 4 3) : K=C4 := by
  have sub : C4⊆K := by
    intro a ha
    rcases (show ∀ i∈C4,i=4 ∨ J.Adj 4 i by decide) a ha with eq|edge
    · exact eq ▸ tip.1
    · by_contra outside
      exact tip.2.2.2.1 ⟨a,mem_sdiff.mpr ⟨mem_univ _,outside⟩,edge⟩
  exact (eq_of_subset_of_card_le sub (by rw [sz]; decide)).symm
theorem stuck4 (z:V) (hz:z∈(U\C4).erase 3) :
    ¬Con G (univ\insert z (C4.erase 4)) := by
  intro connected
  have all : ∀ t∈(U\C4).erase 3,OnEdges G (univ\insert t (C4.erase 4)) (cut4 t) ∧
      ¬ConstantOn (univ\insert t (C4.erase 4)) (cut4 t) := by unfold OnEdges ConstantOn; decide
  obtain ⟨h,n⟩ := all z hz
  exact n (((connected_cuts _ _).mp connected).2 _ h)
theorem winning : F⊆U\{3,4} ∧ F.card=3 ∧ Con G (univ\F) ∧ ∀ q∈F,Dominates G (univ\F) q := by
  refine ⟨by decide,by decide,con 1 (fun i => [88,0,1,1,2,88,3,4,4,6,7,7,5,88][i.val]!) (by decide) (by decide),?_⟩
  unfold Dominates; decide
#print axioms forced3
#print axioms stuck3
#print axioms winning
end Minimal180.Case14
