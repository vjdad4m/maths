import DegreeFiveBalancedCommonRoot189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore shore_off shore_closed from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Two one-place cut shells prevent a small common shore from having
exactly two shared contacts. -/
theorem three_shared_of_small_common_shore_with_one_place_each
    (hc : G.Connected)
    (degree : ∀ u v : V,u≠v → 5  ≤  G.degree u ∨ 5  ≤  G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (shared : 2  ≤  (sharedPortSet C).card)
    (size : (Shore C).card  ≤  (sharedPortSet C).card+3)
    (oneA : (secondShore C a).card  ≤  1) (oneB : (secondShore C b).card  ≤  1) :
    3  ≤  (sharedPortSet C).card := by
  classical
  let S := Shore C
  let K := sharedPortSet C
  let N := S\K
  have k : K⊆S := filter_subset _ _
  have sEq : N.card+K.card=S.card := card_sdiff_add_card_eq_card k
  have k2 : 2 ≤ K.card := shared
  have s5 : S.card ≤ K.card+3 := size
  by_contra! insufficient
  change K.card<3 at insufficient
  have kExact : K.card=2 := by omega
  have inner (w : V) : inside G S w ⊆ S.erase w := by
    intro y ym
    obtain ⟨ys,wy⟩ := mem_filter.mp ym
    exact mem_erase.mpr ⟨wy.ne.symm,ys⟩
  have s4 : 4 ≤ S.card := by
    by_contra! sh
    obtain ⟨u,uk,v,vk,uv⟩ := one_lt_card.mp (show 1<K.card by omega)
    have low (w : V) (wk : w∈K) : G.degree w<5 := by
      have wS := k wk
      have p := card_le_card (inner w)
      rw [card_erase_of_mem wS] at p
      have q := card_le_card (shore_neighbor_cover C wS)
      rw [card_neighborFinset_eq_degree] at q
      change G.degree w ≤ (insert a (insert b (inside G S w))).card at q
      have l := card_insert_le a (insert b (inside G S w))
      have r := card_insert_le b (inside G S w)
      omega
    exact (degree u v uv).elim (fun h=>by have :=low u uk; omega) (fun h=>by have :=low v vk; omega)
  have sz : S.card=5 := by
    by_contra! notFive
    have n2 : 2 ≤ N.card := by omega
    obtain ⟨u,un,v,vn,uv⟩ := one_lt_card.mp (show 1<N.card by omega)
    have low (w : V) (wn : w∈N) : G.degree w<5 := by
      obtain ⟨ws,wK⟩ := mem_sdiff.mp wn
      have no : ¬(G.Adj a w ∧ G.Adj b w) := fun e=>wK (mem_filter.mpr ⟨ws,e⟩)
      have p := card_le_card (inner w)
      rw [card_erase_of_mem ws] at p
      by_contra! h
      have q := inside_high_at_least_four_if_exclusive ws h no
      change 4 ≤ (inside G S w).card at q
      omega
    exact (degree u v uv).elim (fun h=>by have :=low u un; omega) (fun h=>by have :=low v vn; omega)
  let H := N.filter (fun w=>5 ≤ G.degree w)
  have h2 : 2 ≤ H.card := by
    by_contra! fails
    have count : 2 ≤ (N\H).card := by
      have split : (N\H).card+H.card=N.card := card_sdiff_add_card_eq_card (filter_subset _ _)
      omega
    obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<(N\H).card by omega)
    have low (w : V) (wm : w∈N\H) : ¬5 ≤ G.degree w :=
      fun h=>(mem_sdiff.mp wm).2 (mem_filter.mpr ⟨(mem_sdiff.mp wm).1,h⟩)
    exact (degree u v uv).elim (low u um) (low v vm)
  have highUniversal (w : V) (wh : w∈H) : ∀ t∈S,w≠t → G.Adj w t := by
    obtain ⟨wn,hi⟩ := mem_filter.mp wh
    obtain ⟨ws,wo⟩ := mem_sdiff.mp wn
    have n : ¬(G.Adj a w ∧ G.Adj b w) := fun p=>wo (mem_filter.mpr ⟨ws,p⟩)
    have q := inside_high_at_least_four_if_exclusive ws hi n
    change 4 ≤ (inside G S w).card at q
    have eq : inside G S w=S.erase w := eq_of_subset_of_card_le (inner w) (by
      rw [card_erase_of_mem ws]; omega)
    exact fun t ts wt=>(mem_filter.mp (show t∈inside G S w by
      rw [eq]; exact mem_erase.mpr ⟨wt.symm,ts⟩)).2
  obtain ⟨u,uh,v,vh,uv⟩ := one_lt_card.mp (show 1<H.card by omega)
  have un := (mem_filter.mp uh).1
  have vn := (mem_filter.mp vh).1
  have us := (mem_sdiff.mp un).1
  have vs := (mem_sdiff.mp vn).1
  have n3 : N.card=3 := by omega
  have outside : ¬ N⊆({u,v} : Finset V) := by
    intro sub
    have q := card_le_card sub
    rw [show ({u,v} : Finset V).card=2 by simp [uv]] at q
    omega
  obtain ⟨w,wn,wout⟩ := not_subset.mp outside
  have ws := (mem_sdiff.mp wn).1
  have wu : w≠u := fun e=>wout (mem_insert.mpr (.inl e))
  have wv : w≠v := fun e=>wout (mem_insert.mpr (.inr (mem_singleton.mpr e)))
  obtain ⟨x,xK⟩ := card_pos.mp (show 0<K.card by omega)
  obtain ⟨xs,ax,bx⟩ := mem_filter.mp xK
  have miss (c y : V) (cut : c∉S) (cx : G.Adj c x)
      (yh : y∈H) (ny : ¬G.Adj c y) : y∈secondShore C c := by
    have ys := (mem_sdiff.mp (mem_filter.mp yh).1).1
    have cy : c≠y := fun e=>cut (e.symm ▸ ys)
    have yx : y≠x := fun e=>ny (e.symm ▸ cx)
    exact mem_inter.mpr ⟨ys,d2 hc cy ny cx (highUniversal y yh x xs yx).symm⟩
  have contact (c : V) (cut : c∉S) (cx : G.Adj c x)
      (one : (secondShore C c).card ≤ 1) : G.Adj c u ∨ G.Adj c v := by
    by_contra! both
    have h := one_lt_card.mpr ⟨u,miss c u cut cx uh both.1,v,miss c v cut cx vh both.2,uv⟩
    omega
  have aH := contact a (shore_off C).1 ax oneA
  have bH := contact b (shore_off C).2 bx oneB
  have uNon : ¬(G.Adj a u ∧ G.Adj b u) := fun p=>(mem_sdiff.mp un).2 (mem_filter.mpr ⟨us,p⟩)
  have vNon : ¬(G.Adj a v ∧ G.Adj b v) := fun p=>(mem_sdiff.mp vn).2 (mem_filter.mpr ⟨vs,p⟩)
  have prove (c : V) (cut : c∉S) (cx : G.Adj c x) (one : (secondShore C c).card ≤ 1)
      (yes : G.Adj c u ∨ G.Adj c v) (no : ¬G.Adj c u ∨ ¬G.Adj c v) : G.Adj c w := by
    by_contra cw
    have cw' : c≠w := fun e=>cut (e.symm ▸ ws)
    have wshell : w∈secondShore C c := by
      rcases yes with cu|cv
      · exact mem_inter.mpr ⟨ws,d2 hc cw' cw cu (highUniversal u uh w ws wu.symm)⟩
      exact mem_inter.mpr ⟨ws,d2 hc cw' cw cv (highUniversal v vh w ws wv.symm)⟩
    rcases no with nu|nv
    · have h := one_lt_card.mpr ⟨w,wshell,u,miss c u cut cx uh nu,wu⟩
      omega
    have h := one_lt_card.mpr ⟨w,wshell,v,miss c v cut cx vh nv,wv⟩
    omega
  have aw : G.Adj a w := prove a (shore_off C).1 ax oneA aH
    (bH.imp (fun bu au=>uNon ⟨au,bu⟩) (fun bv av=>vNon ⟨av,bv⟩))
  have bw : G.Adj b w := prove b (shore_off C).2 bx oneB bH
    (aH.imp (fun au bu=>uNon ⟨au,bu⟩) (fun av bv=>vNon ⟨av,bv⟩))
  exact (mem_sdiff.mp wn).2 (mem_filter.mpr ⟨ws,aw,bw⟩)

#print axioms three_shared_of_small_common_shore_with_one_place_each
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
