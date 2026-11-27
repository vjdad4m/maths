import RankRepair29
namespace Graffiti384b.Joint17
open Finset SimpleGraph JointRank
open private LowSample.anchor_samples from LowSample384b
open private FiniteRange.bad from FiniteRange384b
open private Repair.omit_set Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def poolNbr (X : Finset V) (v : V) := X.filter (G.Adj v)
private def eligible (X E s : Finset V) := E.filter (fun v => poolNbr G X v⊆s)

/-- Outside an independent set of degree-two vertices, initially retain
the complement of the pool. Remove every ear whose pool neighbors were sampled. -/
theorem trial (X E s : Finset V) (sep : Disjoint X E) (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v)
    (two : ∀ v∈E,G.degree v=2) (sub : s⊆X) :
    gamma G+(X\s).card+(eligible G X E s).card≤Fintype.card V+(FiniteRange.bad G X s).card := by
  classical
  let B := FiniteRange.bad G X s
  let H := (X\s)\B
  let L := eligible G X E s
  let O := H∪L
  have hx : H⊆X := sdiff_subset.trans sdiff_subset
  have le : L⊆E := filter_subset .. 
  have hl : Disjoint H L := sep.mono hx le
  have keep : s⊆Oᶜ := by
    intro i im; apply mem_compl.mpr; intro m
    exact (mem_union.mp m).elim (fun h => (mem_sdiff.mp (mem_sdiff.mp h).1).2 im)
      (fun l => disjoint_left.mp sep (sub im) (le l))
  have safe (v : V) (vo : v∈O) : 2≤nbr G v Oᶜ := by
    rcases mem_union.mp vo with vh|vl
    · obtain ⟨xs,nb⟩ := mem_sdiff.mp vh
      have good : 2≤nbr G v (Xᶜ∪s) := Nat.le_of_not_gt (fun h => nb (mem_filter.mpr ⟨xs,h⟩))
      apply good.trans (card_le_card ?_)
      intro w wm
      obtain ⟨wk,vw⟩ := mem_filter.mp wm
      refine mem_filter.mpr ⟨mem_compl.mpr ?_,vw⟩
      intro wo
      rcases mem_union.mp wo with wh|wl
      · exact (mem_union.mp wk).elim (fun z => mem_compl.mp z (hx wh)) (fun z => mem_compl.mp (keep z) wo)
      · exact (mem_sdiff.mp xs).2 ((mem_filter.mp wl).2 (mem_filter.mpr ⟨(mem_sdiff.mp xs).1,vw.symm⟩))
    · have inc : G.neighborFinset v⊆Oᶜ.filter (G.Adj v) := by
        intro w wm
        have vw := (G.mem_neighborFinset ..).mp wm
        refine mem_filter.mpr ⟨mem_compl.mpr ?_,vw⟩
        intro wo
        rcases mem_union.mp wo with wh|wl
        · exact mem_compl.mp (keep ((mem_filter.mp vl).2 (mem_filter.mpr ⟨hx wh,vw⟩))) wo
        · exact ind v (le vl) w (le wl) vw
      simpa only [card_neighborFinset_eq_degree,two v (le vl),nbr] using card_le_card inc
  have dom := Repair.omit_set G O safe
  have fit : O.card≤Fintype.card V := card_le_univ _
  have os : O.card=H.card+L.card := card_union_of_disjoint hl
  have bs : B⊆X\s := filter_subset ..
  have hs := card_sdiff_add_card_eq_card bs
  change H.card+B.card=(X\s).card at hs
  change gamma G+(X\s).card+L.card≤Fintype.card V+B.card
  omega

/-- Sum the simultaneous ear gains. Each requirement is the exact set of
its neighbors in the sampling pool, irrespective of overlap with another ear. -/
theorem ear_mass (X E : Finset V) (sz : X.card=27) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (n : Fintype.card V=33) (failure : 18≤gamma G) :
    3*4686825+(∑ v∈E,(27-nbr G v X).choose (9-nbr G v X))≤
      ∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard 9
  have kc : K.card=4686825 := by dsimp [K]; rw [card_powersetCard,sz,Nat.choose_eq_fast_choose]; decide
  have each (s : Finset V) (sm : s∈K) : 3+(eligible G X E s).card≤(FiniteRange.bad G X s).card := by
    obtain ⟨sub,k⟩ := mem_powersetCard.mp sm
    have z := trial G X E s sep ind two sub
    rw [card_sdiff sub,sz,k,n] at z; omega
  have z := sum_le_sum each
  simp only [sum_add_distrib,sum_const,smul_eq_mul,kc] at z
  have flip (P : Finset V) (F : Finset V → Finset V) (sub : ∀ s∈K,F s⊆P) :
      (∑ s∈K,(F s).card)=∑ v∈P,(K.filter (fun s => v∈F s)).card := by
    calc _ = ∑ s∈K,∑ v∈P,if v∈F s then 1 else 0 := by
             apply sum_congr rfl; intro s sm; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub s sm)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  rw [flip E (eligible G X E) (fun _ _ => filter_subset ..),flip X (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset)] at z
  have fiber (v : V) (vm : v∈E) : (27-nbr G v X).choose (9-nbr G v X)≤(K.filter (fun s => v∈eligible G X E s)).card := by
    have small : (poolNbr G X v).card≤2 := by
      rw [←two v vm,←card_neighborFinset_eq_degree]
      exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    have lim := LowSample.anchor_samples X (poolNbr G X v) 9 (filter_subset ..) (by omega)
    rw [sz] at lim
    simpa [K,eligible,vm,poolNbr,nbr] using lim
  have gain := sum_le_sum fiber
  change 3*4686825+_≤∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card
  omega

private def row (r : ℕ) := if r<2 then 2288132 else if r<5 then 1776500 else if r<9 then 1311380
  else if r<14 then 923780 else if r<20 then 797810 else 722228

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem table : (∀ r : Fin 27,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
    (r.val+2≤d.val.choose 2 ∨ d.val=10) →
    EarCredit.Pair.loss d (a.val+b.val)+629850*a.val+46189*b.val≤row r) ∧
    (∑ r∈range 27,row r)=29612640 := by
  unfold EarCredit.Pair.loss FiniteRange.badCount row; simp only [Nat.choose_eq_fast_choose]; decide

/-- Each paid incidence to either other ear is counted individually, including
when an exterior vertex is adjacent to both. The rank pays for both charges. -/
theorem ranked (X A F : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v) :
    (∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      629850*(∑ v∈X,nbr G v A)+46189*(∑ v∈X,nbr G v F)≤29612640 := by
  classical
  let bill := fun v => ((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card
  let r := rank X (trianglesAt G)
  have each (v : V) (vm : v∈X) : bill v+629850*nbr G v A+46189*nbr G v F≤row (r v) := by
    have rk := mem_image_of_mem (rank X (trianglesAt G)) vm
    rw [rank_range X _ inj,sz,mem_range] at rk
    have lr := rank_lower X (trianglesAt G) inj 2 lo vm
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right .. 
    have dc : r v+2≤d.choose 2 ∨ d=10 := by
      by_cases hd : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left hd,Nat.add_comm]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have b := EarCredit.Pair.pair_fiber G sz sep vm
    rw [Repair.nbr_add G v af] at b
    have cf' := card_le_card (filter_subset (G.Adj v) F)
    have z := table.1 ⟨r v,rk⟩ ⟨d,by omega⟩ ⟨nbr G v A,by have := ca v vm; omega⟩
      ⟨nbr G v F,by unfold nbr; omega⟩ dc
    exact (Nat.add_le_add_right (Nat.add_le_add_right b _) _).trans z
  have sum := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum] at sum
  rwa [sum_by_rank X _ inj row,sz,table.2] at sum

end Graffiti384b.Joint17
#print axioms Graffiti384b.Joint17.trial
#print axioms Graffiti384b.Joint17.ear_mass
#print axioms Graffiti384b.Joint17.ranked
