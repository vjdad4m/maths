import ExampleBase180

set_option warningAsError true
set_option compiler.extract_closed false
set_option synthInstance.maxSize 4096
namespace Minimal180.Case12
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
noncomputable abbrev hub : Finset V := {0,4,5,6,9,10,11}
private theorem pair_out (K : SimpleGraph V) (sub : J≤K) (S : Finset V) (col : TwoColor K S) :
    ∃ a∈hub, ∃ b∈hub, a≠b ∧ a∉S ∧ b∉S := by
  have dis {a:V} {D:Finset V} (ha:a∈hub) (out:a∉S) (no:¬D⊆S) (inc:D⊆hub.erase a) :
      ∃ p∈hub,∃ q∈hub,p≠q ∧ p∉S ∧ q∉S := by
    obtain ⟨b,hb,ob⟩ := Finset.not_subset.mp no
    obtain ⟨ba,bh⟩ := mem_erase.mp (inc hb)
    exact ⟨a,ha,b,bh,ba.symm,out,ob⟩
  obtain ⟨a,ha,oa⟩ := Finset.not_subset.mp (triangle_excluded K S col 6 10 11
    (sub (by decide)) (sub (by decide)) (sub (by decide)))
  simp only [mem_insert,mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact dis (by decide) oa (five_excluded K S col 4 9 5 11 10
      (sub (by decide)) (sub (by decide)) (sub (by decide)) (sub (by decide)) (sub (by decide))) (by decide)
  · exact dis (by decide) oa (five_excluded K S col 0 6 11 5 9
      (sub (by decide)) (sub (by decide)) (sub (by decide)) (sub (by decide)) (sub (by decide))) (by decide)
  · exact dis (by decide) oa (five_excluded K S col 0 6 10 4 9
      (sub (by decide)) (sub (by decide)) (sub (by decide)) (sub (by decide)) (sub (by decide))) (by decide)

theorem ranks : bipartiteNum J=10 ∧ bipartiteNum G=9 := by
  have cj : TwoColor J (A∪{6,7,8,9}) := by
    refine ⟨A,{6,7,8,9},by decide,rfl,?_,?_⟩ <;> unfold Indep <;> decide
  have cg : TwoColor G (A∪{6,7,9}) := by
    refine ⟨A,{6,7,9},by decide,rfl,?_,?_⟩ <;> unfold Indep <;> decide
  have j₀ := size_bip J cj
  have g₀ := size_bip G cg
  have cJ : (A∪({6,7,8,9}:Finset V)).card=10 := by decide
  have cG : (A∪({6,7,9}:Finset V)).card=9 := by decide
  obtain ⟨S,cS,sS⟩ := optB J
  obtain ⟨T,cT,sT⟩ := optB G
  obtain ⟨a,_,b,_,ab,oa,ob⟩ := pair_out J le_rfl S cS
  obtain ⟨p,hp,q,hq,pq,op,oq⟩ := pair_out G (by rw [←add_eq]; exact le_sup_left) T cT
  obtain ⟨t,ht,ot⟩ := Finset.not_subset.mp (triangle_excluded G T cT 1 7 8 (by decide) (by decide) (by decide))
  have apart {i} (h:i∈hub) : t≠i :=
    (show ∀ v∈({1,7,8}:Finset V),∀ z∈hub,v≠z by decide) t ht i h
  have c₁ := card_le_card (show ({a,b}:Finset V)⊆univ\S by
    intro i h; simp only [mem_insert,mem_singleton] at h; rcases h with rfl|rfl
    · exact mem_sdiff.mpr ⟨mem_univ _,oa⟩
    · exact mem_sdiff.mpr ⟨mem_univ _,ob⟩)
  rw [card_pair ab] at c₁
  have c₂ := card_le_card (show ({t,p,q}:Finset V)⊆univ\T by
    intro i h; simp only [mem_insert,mem_singleton] at h; rcases h with rfl|rfl|rfl
    · exact mem_sdiff.mpr ⟨mem_univ _,ot⟩
    · exact mem_sdiff.mpr ⟨mem_univ _,op⟩
    · exact mem_sdiff.mpr ⟨mem_univ _,oq⟩)
  rw [card_insert_of_not_mem (by simp [apart hp,apart hq]),card_pair pq] at c₂
  have nS := card_sdiff_add_card_eq_card (subset_univ S)
  have nT := card_sdiff_add_card_eq_card (subset_univ T)
  rw [card_univ,Fintype.card_fin] at nS nT
  omega

private noncomputable def visibleArc (i j:V) : Prop := G.Adj i j ∧ d j 0=d i 0+1 ∧ ∀ a,G.Adj a j → d j 0=d a 0+1 → a=i
private noncomputable def safeColor (a b:V) (X:Finset V) : Prop :=
  ∀ e∈((7,8)::oldEdges),e.1∈X → e.2∈X → s(e.1,e.2)=s(a,b)
private theorem critical (a b:V) (X Y:Finset V) (edge:G.Adj a b) (dis:Disjoint X Y)
    (num:(X∪Y).card=10) (sx:safeColor a b X) (sy:safeColor a b Y) :
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

private theorem crit_0_6 : bipartiteNum (G.deleteEdges {s((0:V),6)})=bipartiteNum G+1 := by
  apply critical 0 6 {0,1,2,3,4,5,6} {7,9,10}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_1_7 : bipartiteNum (G.deleteEdges {s((1:V),7)})=bipartiteNum G+1 := by
  apply critical 1 7 {0,1,3,4,5,7} {2,6,8,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_1_8 : bipartiteNum (G.deleteEdges {s((1:V),8)})=bipartiteNum G+1 := by
  apply critical 1 8 {0,1,2,4,5,8} {3,6,7,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_7_8 : bipartiteNum (G.deleteEdges {s((7:V),8)})=bipartiteNum G+1 := by
  apply critical 7 8 {0,1,2,3,4,5} {6,7,8,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_0_9 : bipartiteNum (G.deleteEdges {s((0:V),9)})=bipartiteNum G+1 := by
  apply critical 0 9 {0,3,7,9,10} {1,2,4,5,6}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_4_9 : bipartiteNum (G.deleteEdges {s((4:V),9)})=bipartiteNum G+1 := by
  apply critical 4 9 {0,3,5,7,10} {1,2,4,6,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_5_9 : bipartiteNum (G.deleteEdges {s((5:V),9)})=bipartiteNum G+1 := by
  apply critical 5 9 {0,1,2,4,11} {3,5,6,7,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_4_10 : bipartiteNum (G.deleteEdges {s((4:V),10)})=bipartiteNum G+1 := by
  apply critical 4 10 {0,3,4,5,7,10} {1,2,6,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_6_10 : bipartiteNum (G.deleteEdges {s((6:V),10)})=bipartiteNum G+1 := by
  apply critical 6 10 {0,1,2,3,4,5} {6,7,9,10}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_5_11 : bipartiteNum (G.deleteEdges {s((5:V),11)})=bipartiteNum G+1 := by
  apply critical 5 11 {0,1,2,4,5,11} {3,6,7,9}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_6_11 : bipartiteNum (G.deleteEdges {s((6:V),11)})=bipartiteNum G+1 := by
  apply critical 6 11 {0,1,2,3,4,5} {6,7,9,11}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
private theorem crit_10_11 : bipartiteNum (G.deleteEdges {s((10:V),11)})=bipartiteNum G+1 := by
  apply critical 10 11 {0,7,10,11} {1,2,3,4,5,6}
  all_goals first | unfold safeColor; decide +kernel | decide +kernel
theorem sparse : SparseAt G 0 := by
  let E : Finset (Sym2 V) := {s((0:V),6),s((1:V),7),s((1:V),8),s((7:V),8),s((0:V),9),s((4:V),9),s((5:V),9),s((4:V),10),s((6:V),10),s((5:V),11),s((6:V),11),s((10:V),11)}
  have cover : ∀ a b,G.Adj a b → ¬visibleArc a b → ¬visibleArc b a → s(a,b)∈E := by
    dsimp only [E,visibleArc]; decide +kernel
  intro a b ab no back
  have arc {i j} (h:visibleArc i j) : Arc G 0 i j := by
    simpa only [Arc,(dist_data 0).2,visibleArc] using h
  have which := cover a b ab (fun h => no (arc h)) (fun h => back (arc h))
  simp only [E,mem_insert,mem_singleton] at which
  rcases which with e0|e1|e2|e3|e4|e5|e6|e7|e8|e9|e10|e11
  · rw [e0]; exact crit_0_6
  · rw [e1]; exact crit_1_7
  · rw [e2]; exact crit_1_8
  · rw [e3]; exact crit_7_8
  · rw [e4]; exact crit_0_9
  · rw [e5]; exact crit_4_9
  · rw [e6]; exact crit_5_9
  · rw [e7]; exact crit_4_10
  · rw [e8]; exact crit_6_10
  · rw [e9]; exact crit_5_11
  · rw [e10]; exact crit_6_11
  · rw [e11]; exact crit_10_11

theorem ordinary : ¬violates G := by
  have bound : 6≤maxLeaves G := by
    rw [← weighted_all]
    apply (score_iff_core G (dist_data 0).1 (by decide) univ 6).mpr
    refine ⟨{0,1,2,4,6,7},subset_univ _,by decide,con 3 (fun i => [88,88,88,0,88,2,88,88,1,3,2,1][i.val]!) (by decide) (by decide),?_⟩
    unfold Dominates; decide
  let group (i:V) : Fin 6 := ([0,1,2,3,4,5,0,1,3,4,2,5]:List (Fin 6))[i.val]!
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
end Minimal180.Case12
