import CubicPair
namespace Graffiti384b.TwoEars
open Finset SimpleGraph Simplicial16
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private FiniteRange.bad from FiniteRange384b
open private LowSample.anchor_samples from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A sampled cubic vertex of score two can be removed when its protecting pair
is retained and it has no neighbor among the eligible ears. -/
noncomputable def extra (X E s : Finset V) : Finset V := by
  classical
  exact s.filter (fun v => trianglesAt G v=2 ∧ G.degree v=3 ∧
    nbr G v E=0 ∧ ∃ A,Protects G v A ∧ A⊆Xᶜ∪s)

theorem extra_trial (X E s : Finset V) (sep : Disjoint X E) (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v)
    (two : ∀ v∈E,G.degree v=2) (sub : s⊆X) (hx : X⊆high G)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) :
    gamma G+(X\s).card+(Joint17.eligible G X E s).card+(activated G X s).card+
      (extra G X E s).card≤Fintype.card V+(FiniteRange.bad G X s).card := by
  classical
  let P := extra G X E s
  let t := s\P
  have ps : P⊆s := filter_subset ..
  have ts : t⊆s := sdiff_subset
  have unique {v w : V} (vm : v∈P) (wm : w∈P) : v=w :=
    inj (sub (ps vm)) (sub (ps wm)) ((mem_filter.mp vm).2.1.trans (mem_filter.mp wm).2.1.symm)
  have safe {v w : V} (vp : v∈P) (out : w∉Xᶜ∪t) (near : w=v ∨ G.Adj v w) :
      2≤nbr G w (Xᶜ∪t) := by
    obtain ⟨A,pa,inside⟩ := (mem_filter.mp vp).2.2.2.2
    have keep : A⊆Xᶜ∪t := by
      intro i im; rcases mem_union.mp (inside im) with off|sampled
      · exact mem_union_left _ off
      · exact mem_union_right _ (mem_sdiff.mpr ⟨sampled,fun ip =>
          ((G.mem_neighborFinset ..).mp (pa.2.1 im)).ne (unique vp ip)⟩)
    have sub : A⊆(Xᶜ∪t).filter (G.Adj w) := by
      intro i im; refine mem_filter.mpr ⟨keep im,?_⟩
      rcases near with rfl|vw
      · exact (G.mem_neighborFinset ..).mp (pa.2.1 im)
      · exact (G.mem_neighborFinset ..).mp (pa.2.2 w ((G.mem_neighborFinset ..).mpr vw) (fun m => out (keep m)) im)
    exact pa.1 ▸ card_le_card sub
  have ears : Joint17.eligible G X E s⊆Joint17.eligible G X E t := by
    intro u um
    obtain ⟨ue,hit⟩ := mem_filter.mp um
    apply mem_filter.mpr; refine ⟨ue,?_⟩
    intro v vm
    apply mem_sdiff.mpr; refine ⟨hit vm,?_⟩
    intro vp
    have pos := card_pos.mpr (show (E.filter (G.Adj v)).Nonempty from ⟨u,mem_filter.mpr ⟨ue,(mem_filter.mp vm).2.symm⟩⟩)
    have zero := (mem_filter.mp vp).2.2.2.1
    change nbr G v E>0 at pos; omega
  have old : activated G X s⊆activated G X t := by
    intro v vm
    obtain ⟨vs,sat,credit⟩ := mem_filter.mp vm
    have hi := (mem_filter.mp (hx (sub vs))).2
    have three := Nat.choose_le_choose 2 hi
    have score : 3≤trianglesAt G v := by
      change trianglesAt G v=(G.degree v).choose 2 at sat
      rw [sat]; exact three
    have off : v∉P := fun vp => (by have := (mem_filter.mp vp).2.1; omega)
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨vs,off⟩,sat,credit.trans (card_le_card ?_)⟩
    intro w wm
    obtain ⟨wk,vw⟩ := mem_filter.mp wm
    apply mem_filter.mpr; refine ⟨?_,vw⟩
    rcases mem_union.mp wk with wc|ws
    · exact mem_union_left _ wc
    · apply mem_union_right; apply mem_sdiff.mpr; refine ⟨ws,?_⟩; intro wp
      have big := JointDense.score_of_dominating_neighbor G vw
        (fun x vx xw => CliqueChoice.saturated_clique G sat w x vw vx xw.symm)
      have small := (mem_filter.mp wp).2.1
      omega
  have bad' : FiniteRange.bad G X t⊆FiniteRange.bad G X s := by
    intro v vm
    obtain ⟨vo,low⟩ := mem_filter.mp vm
    obtain ⟨vx,vt⟩ := mem_sdiff.mp vo
    have out : v∉Xᶜ∪t := fun m => (mem_union.mp m).elim (fun h => mem_compl.mp h vx) vt
    have vp : v∉P := fun p => (not_lt_of_ge (safe p out (Or.inl rfl))) low
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨vx,fun vs => vt (mem_sdiff.mpr ⟨vs,vp⟩)⟩,?_⟩
    apply lt_of_le_of_lt (card_le_card ?_) low
    intro w wm
    obtain ⟨wk,vw⟩ := mem_filter.mp wm
    apply mem_filter.mpr; refine ⟨?_,vw⟩
    exact (mem_union.mp wk).elim (mem_union_left _)
      (fun ws => mem_union_right _ (mem_sdiff.mpr ⟨ws,fun wp => (not_lt_of_ge (safe wp out (Or.inr vw.symm))) low⟩))
  have b := Simplicial16.trial G X E t sep ind two (ts.trans sub) hx inj
  have ec := card_le_card ears
  have ac := card_le_card old
  have bc := card_le_card bad'
  have dt : t.card+P.card=s.card := card_sdiff_add_card_eq_card ps
  have sc := card_le_card sub
  rw [card_sdiff (ts.trans sub)] at b
  rw [card_sdiff sub]; change gamma G+_+_+_+P.card≤_; omega

theorem extra_fiber (X E : Finset V) (xs : X.card=28) {v : V} (vx : v∈X)
    (sc : trianglesAt G v=2) (dg : G.degree v=3) (free : nbr G v E=0) :
    1081575≤((X.powersetCard 11).filter (fun s => v∈extra G X E s)).card := by
  classical
  obtain ⟨A,pa⟩ := protecting_pair G dg sc
  let U := insert v (A∩X)
  have ux : U⊆X := insert_subset vx inter_subset_right
  have size : U.card≤3 := (card_insert_le ..).trans (by have := card_le_card (inter_subset_left (s₁:=A) (s₂:=X)); rw [pa.1] at this; omega)
  have c := LowSample.anchor_samples X U 11 ux (by omega)
  have lim : ∀ j : Fin 4,1081575≤(28-j.val).choose (11-j.val) := by simp only [Nat.choose_eq_fast_choose]; decide
  rw [xs] at c
  refine (lim ⟨U.card,by omega⟩).trans (c.trans (card_le_card ?_))
  intro s sm; obtain ⟨sk,us⟩ := mem_filter.mp sm
  refine mem_filter.mpr ⟨sk,mem_filter.mpr ⟨us (mem_insert_self ..),sc,dg,free,A,pa,?_⟩⟩
  intro i ia; by_cases ix : i∈X
  · exact mem_union_right _ (us (mem_insert_of_mem (mem_inter.mpr ⟨ia,ix⟩)))
  · exact mem_union_left _ (mem_compl.mpr ix)
end Graffiti384b.TwoEars
#print axioms Graffiti384b.TwoEars.extra_trial
#print axioms Graffiti384b.TwoEars.extra_fiber
