import Q8ScoreTransfer384b
import Q8AnchorNormalize384b

namespace Graffiti384b.Q8
open Finset SimpleGraph
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000

private def pairsSix : Fin 15→Label×Label :=
  ![(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),
    (5,6),(5,7),(6,7)]

private theorem slot_total : ∀ i j : Label, 2≤i.val→i<j→
    ∃ k : Fin 15,k.val=slot i.val j.val ∧ pairsSix k=(i,j) := by decide

private theorem data_eq : ∀ s : Fin 8,
    let S := forms s
    let T := Graffiti384bQ8.anchorTable s
    (S.edge01=true↔T.1=1) ∧ (if S.edge01 then 1 else 0)=T.1 ∧
      S.d0=T.2.1 ∧ S.d1=T.2.2.1 ∧ S.common=T.2.2.2 := by decide

private theorem degree_triangle_bound {W : Type*} [Fintype W] [DecidableEq W] (J : SimpleGraph W)
    [DecidableRel J.Adj] (v : W) : trianglesAt J v≤(J.degree v).choose 2 := by
  unfold trianglesAt
  exact (card_filter_le _ _).trans_eq (by rw [card_powersetCard,card_neighborFinset_eq_degree])

variable (G : SimpleGraph Label) [DecidableRel G.Adj]

/-- The actual graph supplies the free bits; all anchor rows remain fixed. -/
theorem entries_of_shape (s : Fin 8) (p : Label≃Label)
    (edge01 : G.Adj (p 0) (p 1)↔(Graffiti384bQ8.anchorTable s).1=1)
    (contact : ∀ j : Label,2≤j.val→
      let t := Graffiti384bQ8.anchorTable s
      let a := t.2.1-t.1
      let b := t.2.2.1-t.1
      let c := t.2.2.2
      let r := j.val-2
      (G.Adj (p 0) (p j)↔r<a) ∧
      (G.Adj (p 1) (p j)↔r<c ∨ (a≤r ∧ r<a+b-c))) :
    ∃ bits : Nat→Bool, ∀ i j,adj (forms s) bits i j=true↔G.Adj (p i) (p j) := by
  let bits (k : Nat) := if h:k<15 then
    let t := pairsSix ⟨k,h⟩
    decide (G.Adj (p t.1) (p t.2))
    else false
  refine ⟨bits,?_⟩
  have ordered (i j : Label) (lt : i<j) : adj (forms s) bits i j=true↔G.Adj (p i) (p j) := by
    have ni : i.val < j.val := lt
    dsimp [adj]
    simp only [min_eq_left ni.le,max_eq_right ni.le,if_neg (ne_of_lt ni)]
    have eq := data_eq s
    by_cases z : i.val=0
    · have zi : i=0 := Fin.ext z
      rw [if_pos z]
      by_cases w : j.val=1
      · have wj : j=1 := Fin.ext w
        simpa only [if_pos w,zi,wj] using eq.1.trans edge01.symm
      have up : 2≤j.val := by omega
      rw [if_neg w,zi]
      simpa only [anchorZero,eq.2.1,eq.2.2.1,decide_eq_true_eq] using (contact j up).1.symm
    rw [if_neg z]
    by_cases o : i.val=1
    · have oi : i=1 := Fin.ext o
      have up : 2≤j.val := by omega
      rw [if_pos o,oi]
      simpa only [anchorOne,eq.2.1,eq.2.2.1,eq.2.2.2.1,eq.2.2.2.2,decide_eq_true_eq]
        using (contact j up).2.symm
    rw [if_neg o]
    obtain ⟨k,kVal,matchPair⟩ := slot_total i j (by omega) lt
    rw [←kVal]
    simp only [bits,dif_pos k.isLt,matchPair,decide_eq_true_eq]
  intro i j
  rcases lt_trichotomy i j with lo|same|hi
  · exact ordered i j lo
  · subst j
    simp [adj,G.loopless]
  · have swap : adj (forms s) bits i j = adj (forms s) bits j i := by simp [adj,min_comm,max_comm]
    rw [swap,SimpleGraph.adj_comm]
    exact ordered j i hi

private theorem top_two (positive : ∀ v,0<trianglesAt G v) (distinct : Function.Injective (trianglesAt G)) :
    ∃ x y : Label,x≠y ∧ 7≤trianglesAt G x ∧ 7≤trianglesAt G y ∧
      ∀ z : Label,z≠x→z≠y→trianglesAt G z<trianglesAt G x ∧ trianglesAt G z<trianglesAt G y := by
  obtain ⟨x,_,mx⟩ := exists_max_image (Finset.univ : Finset Label) (trianglesAt G) ⟨0,mem_univ _⟩
  let K := (Finset.univ : Finset Label).erase x
  have kc : K.card=7 := by simp [K]
  obtain ⟨y,ym,my⟩ := exists_max_image K (trianglesAt G) (card_pos.mp (by omega))
  have xy : x≠y := (mem_erase.mp ym).1.symm
  let R := (Finset.range (trianglesAt G y+1)).erase 0
  have sub : K.image (trianglesAt G)⊆R := by
    intro t tm
    obtain ⟨v,vm,rfl⟩ := mem_image.mp tm
    exact mem_erase.mpr ⟨by have := positive v; omega,mem_range.mpr (by have := my v vm; omega)⟩
  have card := card_le_card sub
  rw [card_image_of_injective _ distinct,kc] at card
  have er : 0∈Finset.range (trianglesAt G y+1) := mem_range.mpr (by omega)
  change 7≤R.card at card
  unfold R at card
  rw [card_erase_of_mem er,card_range] at card
  have yg : 7≤trianglesAt G y := by omega
  refine ⟨x,y,xy,yg.trans (mx y (mem_univ _)),yg,?_⟩
  intro z zx zy
  exact ⟨lt_of_le_of_ne (mx z (mem_univ _)) (fun h=>zx (distinct h)),
    lt_of_le_of_ne (my z (mem_erase.mpr ⟨zx,mem_univ _⟩)) (fun h=>zy (distinct h))⟩

private theorem five_degree {v : Label} (score : 7≤trianglesAt G v) : 5≤G.degree v := by
  have le := degree_triangle_bound G v
  by_contra low
  have d4 : G.degree v≤4 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge low)
  have r := Nat.choose_le_choose 2 d4
  have n4 : (4:Nat).choose 2=6 := by decide
  omega

private theorem common_five (x y : Label) (xy : x≠y)
    (num : 5≤(G.neighborFinset x ∩ G.neighborFinset y).card) : gamma G≤3 := by
  obtain ⟨S,sub,sz⟩ := exists_subset_card_eq num
  have count : Sᶜ.card=3 := by rw [card_compl,sz]; decide
  refine Nat.sInf_le ⟨Sᶜ,?_,count⟩
  intro z zo
  have zin : z∈S := by simpa using zo
  have edges := mem_inter.mp (sub zin)
  have xa := (G.mem_neighborFinset _ _).mp edges.1
  have ya := (G.mem_neighborFinset _ _).mp edges.2
  have xo : x∈Sᶜ := mem_compl.mpr (fun xs=>G.loopless x
    ((G.mem_neighborFinset _ _).mp (mem_inter.mp (sub xs)).1))
  have yo : y∈Sᶜ := mem_compl.mpr (fun ys=>G.loopless y
    ((G.mem_neighborFinset _ _).mp (mem_inter.mp (sub ys)).2))
  have pair : ({x,y}:Finset Label)⊆Sᶜ.filter (G.Adj z) :=
    insert_subset (mem_filter.mpr ⟨xo,xa.symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨yo,ya.symm⟩))
  simpa only [card_pair xy] using card_le_card pair

theorem core8_of_covers
    (covers : ∀ (s : Fin 8) (bits : Nat→Bool), Ranked (adj (forms s) bits)→
       ∃ a b c,Dominates3 (adj (forms s) bits) a b c)
    (positive : ∀ v,0<trianglesAt G v)
    (distinct : Function.Injective (trianglesAt G)) : gamma G≤3 := by
  obtain ⟨x,y,xy,xl,yl,top⟩ := top_two G positive distinct
  by_cases large : 5≤(G.neighborFinset x∩G.neighborFinset y).card
  · exact common_five G x y xy large
  obtain ⟨s,p,roots,edge01,contact⟩ := Graffiti384bQ8.normalize_two_anchors G x y xy
    (five_degree G xl) (five_degree G yl) (by omega)
  obtain ⟨b,fit⟩ := entries_of_shape G s p edge01 contact
  have exactScore := score_eq_triangles G p _ fit
  have atAnchor (r : Fin 2) : p (anchor r)=x ∨ p (anchor r)=y := by
    fin_cases r
    · exact roots.imp And.left And.left
    · exact roots.symm.imp And.right And.right
  have rank : Ranked (adj (forms s) b) := by
    refine ⟨fun v=>by rw [exactScore];exact positive _,?_,?_,?_⟩
    · intro v w eq
      rw [exactScore v,exactScore w] at eq
      exact p.injective (distinct eq)
    · intro r
      rw [exactScore]
      rcases atAnchor r with h|h
      · rwa [h]
      · rwa [h]
    · intro v v2 r
      have n (i : Fin 2) : p v≠p (anchor i) := by
        intro h
        have a := congrArg (fun j : Label=>j.val) (p.injective h)
        change v.val=i.val at a
        have lim:=i.isLt
        omega
      have n0 : p v≠p 0 := n 0
      have n1 : p v≠p 1 := n 1
      have nx : p v≠x := by
        rcases roots with ⟨a,_⟩|⟨_,a⟩
        · simpa [a] using n0
        · simpa [a] using n1
      have ny : p v≠y := by
        rcases roots with ⟨_,a⟩|⟨a,_⟩
        · simpa [a] using n1
        · simpa [a] using n0
      rw [exactScore,exactScore]
      rcases atAnchor r with h|h
      · rw [h]
        exact (top _ nx ny).1
      · rw [h]
        exact (top _ nx ny).2
  obtain ⟨a,c,d,h⟩ := covers s b rank
  exact gamma_le_of_dominates3 G p _ fit h

#print axioms entries_of_shape
#print axioms core8_of_covers
end Graffiti384b.Q8
