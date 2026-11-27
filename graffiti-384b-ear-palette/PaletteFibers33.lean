import PaletteContact33

namespace Graffiti384b.EarPalette
open Finset SimpleGraph HighEar JointRank
open private EarPrune.lost_score from EarPrune384b
open private Repair.edge_info Repair.linkEdges Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Score and degree survive deletion of a nonneighbor. -/
private theorem away_values {a v : V} (va : v≠a) (non : ¬H.Adj v a) :
    let W := EarPrune.rest a
    let J := H.induce (W : Set V)
    let z : W := ⟨v,by simpa [W,EarPrune.rest] using va⟩
    trianglesAt J z=trianglesAt H v ∧ J.degree z=H.degree v := by
  classical
  let W := EarPrune.rest a
  let J := H.induce (W : Set V)
  let z : W := ⟨v,by simpa [W,EarPrune.rest] using va⟩
  have empty : ((Repair.linkEdges H v).filter (fun p => a∈p))=∅ := eq_empty_of_forall_not_mem (by
    intro p pm
    obtain ⟨inc,_,_⟩ := Repair.edge_info H (mem_filter.mp pm).1
    exact non ((H.mem_neighborFinset _ _).mp (inc (mem_filter.mp pm).2)))
  have score := EarPrune.lost_score H a z
  change trianglesAt J z+((Repair.linkEdges H v).filter (fun p => a∈p)).card=trianglesAt H v at score
  rw [empty,card_empty,Nat.add_zero] at score
  have same : W.filter (H.Adj v)=H.neighborFinset v := by
    ext w; simp only [mem_filter,H.mem_neighborFinset,W,EarPrune.rest,mem_compl,mem_singleton]
    exact ⟨And.right,fun h => ⟨fun eq => non (eq ▸ h),h⟩⟩
  have d := EarAnchor.induced_degree H z
  change J.degree z=(W.filter (H.Adj v)).card at d
  rw [same,card_neighborFinset_eq_degree] at d
  exact ⟨score,d⟩

/-- Deleting a vertex common to all five-cliques preserves the triangle
count and the degree at every other vertex not adjacent to it. -/
theorem away_turan {c v : V} (vc : v≠c) (non : ¬H.Adj v c)
    (hit : ∀ C,H.IsNClique 5 C → c∈C) :
    trianglesAt H v≤(turanGraph (H.degree v) 3).edgeFinset.card := by
  classical
  let W := EarPrune.rest c
  let J := H.induce (W : Set V)
  let z : W := ⟨v,by simpa [W,EarPrune.rest] using vc⟩
  let emb : W ↪ V := Function.Embedding.subtype _
  have free : J.CliqueFree 5 := by
    intro D cl
    have lifted : H.IsNClique 5 (D.map emb) := cl.map.mono (H.spanningCoe_induce_le (s:=(W : Set V)))
    obtain ⟨x,_,m⟩ := mem_map.mp (hit _ lifted)
    exact mem_compl.mp x.property (mem_singleton.mpr m)
  obtain ⟨score,d⟩ := away_values H vc non
  change trianglesAt J z=trianglesAt H v at score
  change J.degree z=H.degree v at d
  have cap := RankTuran.local_turan J 3 (by decide) free z
  rwa [d,score] at cap


/-- If a pair meets every five-clique, a vertex adjacent to neither member
satisfies the same local Turán bound as in a five-clique-free graph. -/
theorem pair_turan {a c v : V} (ac : a≠c) (va : v≠a) (vc : v≠c)
    (na : ¬H.Adj v a) (nc : ¬H.Adj v c) (hit : ∀ C,H.IsNClique 5 C → a∈C ∨ c∈C) :
    trianglesAt H v≤(turanGraph (H.degree v) 3).edgeFinset.card := by
  classical
  let W := EarPrune.rest a
  let J := H.induce (W : Set V)
  let u : W := ⟨v,by simpa [W,EarPrune.rest] using va⟩
  let z : W := ⟨c,by simpa [W,EarPrune.rest] using ac.symm⟩
  let emb : W ↪ V := Function.Embedding.subtype _
  have alone (D : Finset W) (cl : J.IsNClique 5 D) : z∈D := by
    have lifted : H.IsNClique 5 (D.map emb) := cl.map.mono (H.spanningCoe_induce_le (s:=(W : Set V)))
    rcases hit _ lifted with am|cm
    · obtain ⟨x,_,eq⟩ := mem_map.mp am
      exact (mem_compl.mp x.property (mem_singleton.mpr eq)).elim
    · obtain ⟨x,xm,eq⟩ := mem_map.mp cm
      exact (show x=z from Subtype.ext eq) ▸ xm
  have cap := away_turan J (c:=z) (v:=u) (fun eq => vc (congrArg Subtype.val eq)) nc alone
  obtain ⟨score,degree⟩ := away_values H va na
  change trianglesAt J u=trianglesAt H v at score
  change J.degree u=H.degree v at degree
  rwa [score,degree] at cap

/-- With a guaranteed retained neighbor, the deficient samples avoid the
vertex and all its neighbors in the pool. -/
theorem credited_count {W : Finset V} {v c : V} (vm : v∈W) (vc : H.Adj v c) (cm : c∉W)
    (inc : H.neighborFinset v⊆insert c W) (b : ℕ) :
    ((W.powersetCard b).filter (fun k => v∈FiniteRange.bad H W k)).card≤
      (W.card-H.degree v).choose b := by
  classical
  let N := (H.neighborFinset v).erase c
  have inN : N⊆W.erase v := by
    intro w wm
    obtain ⟨wc,wn⟩ := mem_erase.mp wm
    exact mem_erase.mpr ⟨fun eq => H.not_mem_neighborFinset_self v (eq ▸ wn),(mem_insert.mp (inc wn)).resolve_left wc⟩
  let S := W.erase v\N
  have nc : c∈H.neighborFinset v := (H.mem_neighborFinset _ _).mpr vc
  have ns : N.card=H.degree v-1 := by rw [show N=_ from rfl,card_erase_of_mem nc,card_neighborFinset_eq_degree]
  have nd : 0<H.degree v := by rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨c,nc⟩
  have ws : 0<W.card := card_pos.mpr ⟨v,vm⟩
  have ss : S.card=W.card-H.degree v := by
    rw [show S=W.erase v\N from rfl,card_sdiff inN,card_erase_of_mem vm,ns]; omega
  have sub : (W.powersetCard b).filter (fun k => v∈FiniteRange.bad H W k)⊆S.powersetCard b := by
    intro k km
    obtain ⟨sample,fail⟩ := mem_filter.mp km
    obtain ⟨kw,kb⟩ := mem_powersetCard.mp sample
    obtain ⟨out,small⟩ := mem_filter.mp fail
    apply mem_powersetCard.mpr ⟨?_,kb⟩
    intro w wk
    refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun eq => (mem_sdiff.mp out).2 (eq ▸ wk),kw wk⟩,?_⟩
    intro wn
    obtain ⟨wc,rel⟩ := mem_erase.mp wn
    have two := PinnedColor34.two H wc ((H.mem_neighborFinset _ _).mp rel) vc
      (mem_union_right Wᶜ wk) (mem_union_left k (mem_compl.mpr cm))
    omega
  have bound := card_le_card sub
  rwa [card_powersetCard,ss] at bound

def threshold (i : ℕ) := if i<3 then i+2 else i+3

def floorDegree (i : ℕ) := if i<2 then 3 else if i<3 then 4 else if i<6 then 5 else
  if i<10 then 6 else if i<14 then 7 else if i<19 then 8 else if i<25 then 9 else 10

def cost (i : ℕ) := FiniteRange.badCount 29 10 (floorDegree i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem table : (∀ i : Fin 27,∀ d : Fin 11,
    ((threshold i≤RankTable.cap d 3 ∨ d.val=10) → FiniteRange.badCount 29 10 d≤cost i) ∧
    ((threshold i≤d.val.choose 2 ∨ d.val=10) → (29-d.val).choose 10≤cost i)) ∧
    (∑ i∈range 27,cost i)=80087034 ∧ 80087034<4*(29:ℕ).choose 10 := by
  unfold threshold RankTable.cap cost floorDegree FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

/-- The cost table charges each tested vertex according to its score rank,
with a separate bound for vertices adjacent to the fixed anchor. -/
theorem rank_fiber {v : V} {W : Finset V} (ws : W.card=29) (vm : v∈W)
    (apart : (∀ w,w∉W → ¬H.Adj v w) → trianglesAt H v≤(turanGraph (H.degree v) 3).edgeFinset.card)
    {i : ℕ} (lt : i<27) (score : threshold i≤trianglesAt H v) :
    ((W.powersetCard 10).filter (fun k => v∈FiniteRange.bad H W k)).card≤cost i := by
  let d := min (H.degree v) 10
  have lo : d≤H.degree v := min_le_left .. 
  have hi : d≤10 := min_le_right ..
  have same (ne : d≠10) : d=H.degree v := by dsimp [d] at *; omega
  obtain ⟨plain,cred⟩ := table.1 ⟨i,lt⟩ ⟨d,by omega⟩
  change (threshold i≤RankTable.cap d 3 ∨ d=10 → FiniteRange.badCount 29 10 d≤cost i) at plain
  change (threshold i≤d.choose 2 ∨ d=10 → (29-d).choose 10≤cost i) at cred
  by_cases credit : ∃ c,c∉W ∧ H.Adj v c
  · obtain ⟨c,cm,vc⟩ := credit
    by_cases inc : H.neighborFinset v⊆insert c W
    swap
    · obtain ⟨z,zn,off⟩ := not_subset.mp inc
      obtain ⟨zc,zm⟩ := (show z≠c ∧ z∉W by simpa [not_or] using off)
      have empty : ((W.powersetCard 10).filter (fun k => v∈FiniteRange.bad H W k))=∅ := eq_empty_of_forall_not_mem (by
        intro k km
        have low := (mem_filter.mp (mem_filter.mp km).2).2
        have two := PinnedColor34.two H zc ((H.mem_neighborFinset _ _).mp zn) vc
          (mem_union_left k (mem_compl.mpr zm)) (mem_union_left k (mem_compl.mpr cm))
        omega)
      rw [empty,card_empty]; exact Nat.zero_le _
    have cap := credited_count H vm vc cm inc 10
    rw [ws] at cap
    have val : (29-d).choose 10≤cost i := by
      apply cred; by_cases dm : d=10
      · exact Or.inr dm
      · apply Or.inl; rw [same dm]; exact score.trans (Repair.triangles_le_choose H v)
    exact cap.trans ((Nat.choose_le_choose 10 (by omega : 29-H.degree v≤29-d)).trans val)
  · have cap := FiniteRange.count_bad H W 10 d v vm lo (by rw [ws]; omega)
    rw [ws] at cap
    apply cap.trans; apply plain; by_cases dm : d=10
    · exact Or.inr dm
    · have up := apart (fun w wm edge => credit ⟨w,wm,edge⟩)
      have num := RankTable.cap_table ⟨d,by omega⟩ ⟨3,by decide⟩ (by decide)
      change (turanGraph d 3).edgeFinset.card=RankTable.cap d 3 at num
      rw [← same dm] at up
      exact Or.inl (score.trans (up.trans_eq num))

theorem sum_cost : (∑ i∈range 27,cost i)<4*(29:ℕ).choose 10 :=
  table.2.1 ▸ table.2.2

end Graffiti384b.EarPalette
#print axioms Graffiti384b.EarPalette.away_turan
#print axioms Graffiti384b.EarPalette.pair_turan
#print axioms Graffiti384b.EarPalette.credited_count
#print axioms Graffiti384b.EarPalette.rank_fiber
#print axioms Graffiti384b.EarPalette.sum_cost
