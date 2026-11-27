import Indexed183
import DegreeTwoClass

namespace Graffiti183.Exceptional
open Finset SimpleGraph Short177 Graffiti179

set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable [DecidableRel G.Adj]

structure LargestBlock (seed : Finset V) extends Graffiti179.Block G univ seed where
  largest : ∀ S : Finset V, seed ⊆ S → Graffiti177.Con G S → TwoColor G S →
    S.card ≤ (A ∪ B).card

omit [Fintype V] [DecidableRel G.Adj] in
private theorem indep_insert_safe {I : Finset V} (hI : Indep G I) {x : V}
    (safe : ∀ y ∈ I, ¬ G.Adj x y) : Indep G (insert x I) := by
  intro a ha b hb ne e
  rcases mem_insert.mp ha with rfl | aa <;> rcases mem_insert.mp hb with rfl | bb
  · exact ne rfl
  · exact safe _ bb e
  · exact safe _ aa e.symm
  · exact hI _ aa _ bb ne e

omit [DecidableRel G.Adj] in
theorem exists_largest_block {seed : Finset V} (hconn : Graffiti177.Con G seed)
    (hbip : TwoColor G seed) : Nonempty (LargestBlock G seed) := by
  classical
  let candidates := (univ : Finset (Finset V)).filter
    (fun S => seed ⊆ S ∧ Graffiti177.Con G S ∧ TwoColor G S)
  have seed_mem : seed ∈ candidates := mem_filter.mpr ⟨mem_univ _,Subset.rfl,hconn,hbip⟩
  obtain ⟨S,hS,best⟩ := exists_max_image candidates Finset.card ⟨seed,seed_mem⟩
  obtain ⟨hsSeed,hsConn,A,B,d,e,i,j⟩ := (mem_filter.mp hS).2
  subst S
  have largest (R : Finset V) (hsub : seed ⊆ R) (hc : Graffiti177.Con G R)
      (ht : TwoColor G R) : R.card ≤ (A ∪ B).card :=
    best _ (mem_filter.mpr ⟨mem_univ _,hsub,hc,ht⟩)
  refine ⟨⟨⟨A,B,d,i,j,hsConn,subset_univ _,hsSeed,?_⟩,largest⟩⟩
  intro x _ xn hx
  obtain ⟨y,ym,ey⟩ := hx
  have conn' := Graffiti177.con_insert G hsConn ym ey
  have hbig (colors : TwoColor G (insert x (A ∪ B))) : False := by
    have le := largest _ (hsSeed.trans (subset_insert _ _)) conn' colors
    rw [card_insert_of_not_mem xn] at le
    omega
  constructor
  · by_contra! h
    have ds : Disjoint (insert x A) B := disjoint_insert_left.mpr
      ⟨fun xB => xn (mem_union_right _ xB),d⟩
    exact hbig ⟨insert x A,B,ds,insert_union _ _ _, indep_insert_safe G i h,j⟩
  · by_contra! h
    have ds : Disjoint A (insert x B) := disjoint_insert_right.mpr
      ⟨fun xA => xn (mem_union_left _ xA),d⟩
    exact hbig ⟨A,insert x B,ds,union_insert _ _ _,i,indep_insert_safe G j h⟩

/-- The equality budget forces an exterior vertex whose contacts are exactly
the two vertices of any removable pair in the block. -/
theorem exact_blocker {seed : Finset V} (b : Graffiti179.Block G univ seed)
    (hc : G.Connected) (hf : ¬ Claim183 G) {a d : V}
    (ha : a ∈ b.A ∪ b.B) (hd : d ∈ b.A ∪ b.B) (ne : a ≠ d)
    (con : Graffiti177.Con G ((b.A ∪ b.B) \ {a,d}))
    (da : Graffiti177.Dominates G ((b.A ∪ b.B) \ {a,d}) a)
    (dd : Graffiti177.Dominates G ((b.A ∪ b.B) \ {a,d}) d) :
    ∃ x ∉ b.A ∪ b.B, ∀ y ∈ b.A ∪ b.B, G.Adj x y ↔ y = a ∨ y = d := by
  classical
  by_contra! h
  apply hf ((metric_upper_bound hc).trans ?_)
  apply two_gain_from_block G b hc ha hd ne con da dd
  rintro ⟨x,hx,ea,ed,only⟩
  have exact_adj (y : V) (hy : y ∈ b.A ∪ b.B) : G.Adj x y ↔ y = a ∨ y = d := by
    constructor
    · intro e
      by_contra! hn
      exact only y (mem_sdiff.mpr ⟨hy,by simp [hn.1,hn.2]⟩) e
    · rintro (rfl | rfl)
      · exact ea
      · exact ed
  obtain ⟨y,hy,neq⟩ := h x hx
  rcases neq with ⟨e,hna,hnd⟩ | ⟨ne,h⟩
  · exact (exact_adj y hy).mp e |>.elim hna hnd
  · exact ne ((exact_adj y hy).mpr h)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem independent_neighbors_in_coloring {S : Finset V} (color : TwoColor G S)
    {v x y : V} (hv : v ∈ S) (hx : x ∈ S) (hy : y ∈ S)
    (ex : G.Adj v x) (ey : G.Adj v y) : ¬ G.Adj x y := by
  obtain ⟨A,B,_,rfl,ia,ib⟩ := color
  rcases mem_union.mp hv with vA | vB
  · have xB := (mem_union.mp hx).resolve_left (fun xA => ia _ vA _ xA ex.ne ex)
    have yB := (mem_union.mp hy).resolve_left (fun yA => ia _ vA _ yA ey.ne ey)
    exact fun e => ib _ xB _ yB e.ne e
  · have xA := (mem_union.mp hx).resolve_right (fun xB => ib _ vB _ xB ex.ne ex)
    have yA := (mem_union.mp hy).resolve_right (fun yB => ib _ vB _ yB ey.ne ey)
    exact fun e => ia _ xA _ yA e.ne e

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every connected induced bipartite set in a claw-free graph has a path
or cycle indexing, using the degree-two classification from #260. -/
theorem block_index {S : Finset V} (hc : Graffiti177.Con G S)
    (hb : TwoColor G S) (hclaw : ClawFree G) (hn : 6 ≤ S.card) :
    ∃ m : ℕ, 6 ≤ m ∧ ∃ f : Fin m ↪ V, indexSet f = S ∧
      (∀ i j, G.Adj (f i) (f j) ↔ PathAdj i j) ∨
      indexSet f = S ∧ (∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) := by
  classical
  let H := G.induce (S : Set V)
  have ct : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  have hdeg (v : S) : (Graffiti271.nbr H v).card ≤ 2 := by
    by_contra! too
    obtain ⟨x,hx,y,hy,z,hz,xy,xz,yz⟩ := Finset.two_lt_card.mp too
    have ex : G.Adj v.val x.val := (Graffiti271.mem_nbr H).mp hx
    have ey : G.Adj v.val y.val := (Graffiti271.mem_nbr H).mp hy
    have ez : G.Adj v.val z.val := (Graffiti271.mem_nbr H).mp hz
    have na := independent_neighbors_in_coloring G hb v.prop x.prop y.prop ex ey
    have nb := independent_neighbors_in_coloring G hb v.prop x.prop z.prop ex ez
    have nc := independent_neighbors_in_coloring G hb v.prop y.prop z.prop ey ez
    exact nc (hclaw ex ey ez (fun eq => xy (Subtype.ext eq))
      (fun eq => xz (Subtype.ext eq)) (fun eq => yz (Subtype.ext eq)) na nb)
  obtain ⟨k,_,e,wrap,adj⟩ := GraffitiDegreeTwo.degree_two_indexed H hc (by omega) hdeg
  let f : Fin (k+1) ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  have cm : k+1 = S.card := by simpa [ct] using Fintype.card_congr e
  have hf : indexSet f = S := by
    ext v
    rw [mem_indexSet]
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).prop
    · intro hv
      obtain ⟨i,hi⟩ := e.surjective ⟨v,hv⟩
      exact ⟨i,congrArg Subtype.val hi⟩
  refine ⟨k+1,by omega,f,?_⟩
  by_cases hw : wrap
  · right
    refine ⟨hf,fun i j => ?_⟩
    change H.Adj (e i) (e j) ↔ CycleAdj i j
    rw [adj]
    simp only [hw,true_and,CycleAdj]
    omega
  · left
    refine ⟨hf,fun i j => ?_⟩
    change H.Adj (e i) (e j) ↔ PathAdj i j
    rw [adj]
    simp only [hw,false_and,or_false,PathAdj]

#print axioms exists_largest_block
#print axioms exact_blocker
#print axioms block_index
end Graffiti183.Exceptional
