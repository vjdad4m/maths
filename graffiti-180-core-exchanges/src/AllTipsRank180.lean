import AllTipsBase180
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
namespace Minimal180.Case14
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180

private theorem missing {k : ℕ} (K : SimpleGraph V) (S : Finset V) (col : TwoColor K S)
    (a b c : Fin k→V) (tag : V→ℕ)
    (h : ∀ i,K.Adj (a i) (b i) ∧ K.Adj (b i) (c i) ∧ K.Adj (c i) (a i) ∧
      tag (a i)=i.val ∧ tag (b i)=i.val ∧ tag (c i)=i.val) :
    k≤(univ\S).card := by
  classical
  have out (i:Fin k) : ∃ v∈(univ\S),tag v=i.val := by
    obtain ⟨ab,bc,ca,ta,tb,tc⟩ := h i
    obtain ⟨v,tri,notS⟩ := Finset.not_subset.mp (triangle_excluded K S col (a i) (b i) (c i) ab bc ca)
    refine ⟨v,mem_sdiff.mpr ⟨mem_univ _,notS⟩,?_⟩
    simp only [mem_insert,mem_singleton] at tri
    rcases tri with hu|hu|hu
    · exact hu ▸ ta
    · exact hu ▸ tb
    · exact hu ▸ tc
  choose f outside tagf using out
  have card : (univ:Finset (Fin k)).card≤(univ\S).card := by
    apply card_le_card_of_injOn f (fun i _ => outside i)
    intro i _ j _ eq
    exact Fin.ext ((tagf i).symm.trans ((congrArg tag eq).trans (tagf j)))
  simpa using card

private theorem lowerRank : bipartiteNum J=11 := by
  let X : Finset V := {0,3,4,7,9}
  let Y : Finset V := {1,5,6,11,12,13}
  have col : TwoColor J (X∪Y) := by
    refine ⟨X,Y,by decide,rfl,?_,?_⟩ <;> unfold Indep <;> decide
  have lo := size_bip J col
  have size : (X∪Y).card=11 := by decide
  obtain ⟨S,cs,num⟩ := optB J
  have absent := missing (k:=3) J S cs
    (fun i => [0,6,9][i.val]!) (fun i => [1,7,10][i.val]!) (fun i => [2,8,11][i.val]!)
    (fun v => ([0,0,0,0,0,0,1,1,1,2,2,2,0,0]:List ℕ)[v.val]!) (by decide)
  have total := card_sdiff_add_card_eq_card (subset_univ S)
  rw [card_univ,Fintype.card_fin] at total
  omega

private theorem upperRank : bipartiteNum G=10 := by
  let X : Finset V := {0,3,6,10,12}
  let Y : Finset V := {1,4,7,9,13}
  have col : TwoColor G (X∪Y) := by
    refine ⟨X,Y,by decide,rfl,?_,?_⟩ <;> unfold Indep <;> decide
  have lo := size_bip G col
  have size : (X∪Y).card=10 := by decide
  obtain ⟨S,cs,num⟩ := optB G
  have absent := missing (k:=4) G S cs
    (fun i => [0,3,6,9][i.val]!) (fun i => [1,4,7,10][i.val]!) (fun i => [2,5,8,11][i.val]!)
    (fun v => ([0,0,0,1,1,1,2,2,2,3,3,3,0,0]:List ℕ)[v.val]!) (by decide)
  have total := card_sdiff_add_card_eq_card (subset_univ S)
  rw [card_univ,Fintype.card_fin] at total
  omega
theorem ranks : bipartiteNum J=11 ∧ bipartiteNum G=10 := ⟨lowerRank,upperRank⟩
private noncomputable def visibleArc (i j:V) : Prop := G.Adj i j ∧ d j 11=d i 11+1 ∧ ∀ a,G.Adj a j → d j 11=d a 11+1 → a=i
private noncomputable def safeColor (a b:V) (X:Finset V) : Prop :=
  ∀ e∈((3,4)::oldEdges),e.1∈X → e.2∈X → s(e.1,e.2)=s(a,b)
private theorem critical (a b:V) (X Y:Finset V) (edge:G.Adj a b) (dis:Disjoint X Y)
    (num:(X∪Y).card=11) (sx:safeColor a b X) (sy:safeColor a b Y) :
    bipartiteNum (G.deleteEdges {s(a,b)})=bipartiteNum G+1 := by
  let H := G.deleteEdges {s(a,b)}
  have ind {Z:Finset V} (ok:safeColor a b Z) : Indep H Z := by
    intro i hi j hj _ e
    obtain ⟨old,neq⟩ := deleteEdges_adj.mp e
    apply neq
    change s(i,j)=s(a,b)
    rcases old.2 with f|f
    · exact ok (i,j) f hi hj
    · exact Sym2.eq_swap.trans (ok (j,i) f hj hi)
  have col : TwoColor H (X∪Y) := ⟨X,Y,dis,rfl,ind sx,ind sy⟩
  have lo := size_bip H col
  exact (edge_witness G a b edge (by change bipartiteNum G<bipartiteNum H; rw [ranks.2]; omega)).1

private theorem crit_1_2 : bipartiteNum (G.deleteEdges {s((1:V),2)})=bipartiteNum G+1 := by
  apply critical 1 2 {0,3,6,10,12} {1,2,4,7,9,13}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_3_4 : bipartiteNum (G.deleteEdges {s((3:V),4)})=bipartiteNum G+1 := by
  apply critical 3 4 {0,3,4,7,9} {1,5,6,11,12,13}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_3_5 : bipartiteNum (G.deleteEdges {s((3:V),5)})=bipartiteNum G+1 := by
  apply critical 3 5 {0,3,5,6,10,12} {1,4,7,9,13}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_4_5 : bipartiteNum (G.deleteEdges {s((4:V),5)})=bipartiteNum G+1 := by
  apply critical 4 5 {0,3,6,10,12} {1,4,5,7,9,13}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_6_8 : bipartiteNum (G.deleteEdges {s((6:V),8)})=bipartiteNum G+1 := by
  apply critical 6 8 {0,3,6,8,10,12} {1,4,7,9,13}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_9_10 : bipartiteNum (G.deleteEdges {s((9:V),10)})=bipartiteNum G+1 := by
  apply critical 9 10 {0,3,6,9,10} {1,4,8,11,12,13}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
theorem sparse : SparseAt G 11 := by
  let E : Finset (Sym2 V) := {s((1:V),2),s((3:V),4),s((3:V),5),s((4:V),5),s((6:V),8),s((9:V),10)}
  have cover : ∀ a b,G.Adj a b → ¬visibleArc a b → ¬visibleArc b a → s(a,b)∈E := by
    dsimp only [E,visibleArc]; decide +kernel
  intro a b ab no back
  have arc {i j} (h:visibleArc i j) : Arc G 11 i j := by
    simpa only [Arc,(dist_data 11).2,visibleArc] using h
  have which := cover a b ab (fun h => no (arc h)) (fun h => back (arc h))
  simp only [E,mem_insert,mem_singleton] at which
  rcases which with e0|e1|e2|e3|e4|e5
  · rw [e0]; exact crit_1_2
  · rw [e1]; exact crit_3_4
  · rw [e2]; exact crit_3_5
  · rw [e3]; exact crit_4_5
  · rw [e4]; exact crit_6_8
  · rw [e5]; exact crit_9_10
theorem ordinary : ¬violates G := by
  have bound : 6≤maxLeaves G := by
    rw [← weighted_all]
    apply (score_iff_core G (dist_data 11).1 (by decide) univ 6).mpr
    refine ⟨{0,2,5,8,11,13},subset_univ _,by decide,con 1 (fun i => [88,0,88,1,2,88,3,4,88,6,7,88,5,88][i.val]!) (by decide) (by decide),?_⟩
    unfold Dominates; decide
  let group (i:V) : Fin 6 := ([0,0,0,1,1,1,2,2,2,3,3,3,4,5]:List (Fin 6))[i.val]!
  obtain ⟨I,ind,num⟩ := exists_max_indep G
  have cap : I.card≤(univ:Finset (Fin 6)).card := by
    apply card_le_card_of_injOn group (fun _ _ => mem_univ _)
    intro i hi j hj eq
    by_contra ne
    exact ind i hi j hj ne ((show ∀ a b,a≠b → group a=group b → G.Adj a b by dsimp only [group]; decide +kernel) i j ne eq)
  rw [card_univ,Fintype.card_fin] at cap
  have even : maxEven G≤8 := by
    apply Finset.sup_le
    intro r _
    rw [even_equiv]
    have eq : parity G r false=univ.filter (fun i => d i r%2=0) := by
      ext i; simp only [mem_parity,(dist_data r).2,mem_filter,mem_univ,true_and,Bool.toNat_false]
    rw [eq]; exact (show ∀ j : V,(univ.filter (fun i => d i j%2=0)).card≤8 by decide) r
  unfold violates
  rw [ranks.2]
  omega

#print axioms ranks
#print axioms sparse
#print axioms ordinary
end Minimal180.Case14
