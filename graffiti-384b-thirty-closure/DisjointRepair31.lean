import DisjointRotation31
import DisjointGeometry31

namespace Graffiti384b.Disjoint30.Board
open Finset SimpleGraph
open private ForcedCubics.third_contact from SharedSaving33
open private Repair.nbr_add Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Board G)
def extra (x y : V) (k : Finset V) :=
  ({x}:Finset V).filter (fun w => nbr G w k+nbr G w (M.pins x y)<2)

def failed (x y : V) (k : Finset V) := Disjoint30.failures G M.W k (fun v => nbr G v (M.pins x y))


private theorem one_U {x : V} (xm : x∈M.U) : 1≤nbr G x (M.U.erase x) := by
  have hc : (M.U.erase x).card=2 := by rw [card_erase_of_mem xm,M.sizes.1]
  obtain ⟨p,pm,q,qm,pq⟩ := one_lt_card.mp (show 1<(M.U.erase x).card by omega)
  obtain ⟨px,pu⟩ := mem_erase.mp pm
  obtain ⟨qx,qu⟩ := mem_erase.mp qm
  rcases ForcedCubics.third_contact G M.du M.su.ge pq ((G.mem_neighborFinset ..).mp pu)
    ((G.mem_neighborFinset ..).mp qu) ((G.mem_neighborFinset ..).mp xm) px.symm qx.symm with edge|edge
  · exact card_pos.mpr ⟨p,mem_filter.mpr ⟨pm,edge⟩⟩
  · exact card_pos.mpr ⟨q,mem_filter.mpr ⟨qm,edge⟩⟩

private theorem retained {x y : V} (xm : x∈M.U) (ym : y∈M.L) :
    (M.pins x y).card≤4 ∧ 2≤nbr G M.u (M.pins x y) ∧ 2≤nbr G M.s (M.pins x y) ∧
      2≤nbr G y (M.pins x y) ∧ 1≤nbr G x (M.pins x y) := by
  have X : (M.U.erase x).card=2 := by rw [card_erase_of_mem xm,M.sizes.1]
  have Y : (M.L.erase y).card=2 := by rw [card_erase_of_mem ym,M.sizes.2]
  have xp : M.U.erase x⊆M.pins x y := subset_union_left
  have yp : M.L.erase y⊆M.pins x y := subset_union_right
  have a := card_union_le (M.U.erase x) (M.L.erase y)
  change (M.pins x y).card≤_ at a
  have uu : nbr G M.u (M.U.erase x)=2 := by
    unfold nbr; rw [filter_true_of_mem (s:=M.U.erase x) (fun z zm => (G.mem_neighborFinset ..).mp (mem_erase.mp zm).2),X]
  have ss : nbr G M.s (M.L.erase y)=2 := by
    unfold nbr; rw [filter_true_of_mem (s:=M.L.erase y) (fun z zm => (G.mem_neighborFinset ..).mp (mem_erase.mp zm).2),Y]
  have yy : nbr G y (M.L.erase y)=2 := by
    unfold nbr; rw [filter_true_of_mem (s:=M.L.erase y) (fun z zm => EarAnchor.full_neighbors G M.ds M.ss
      ((G.mem_neighborFinset ..).mp ym) ((G.mem_neighborFinset ..).mp (mem_erase.mp zm).2) (mem_erase.mp zm).1.symm),Y]
  exact ⟨by omega,uu ▸ Repair.nbr_mono G _ xp,ss ▸ Repair.nbr_mono G _ yp,
    yy ▸ Repair.nbr_mono G _ yp,(M.one_U xm).trans (Repair.nbr_mono G _ xp)⟩

/-- Any particular sample extends to a 2-dominating set by the indicated repairs. -/
theorem trial {x y : V} (xm : x∈M.U) (ym : y∈M.L) {k : Finset V} (km : k∈M.W.powersetCard 8) :
    gamma G≤12+(M.failed x y k).card+(M.extra x y k).card := by
  classical
  let P := M.pins x y
  let T := ((P∪k)∪M.failed x y k)∪M.extra x y k
  have front : P∪k⊆T := subset_union_left.trans subset_union_left
  have keep : P⊆T := subset_union_left.trans front
  have ⟨sz,u2,s2,y2,_⟩ := M.retained xm ym
  obtain ⟨kw,ks⟩ := mem_powersetCard.mp km
  have dis : Disjoint P k := disjoint_left.mpr (fun z zp zk => ((M.outside z).mp (kw zk)).2.2 (M.pin_subset x y zp))
  have dom : TwoDominates G T := by
    intro v out
    by_cases wm : v∈M.W
    · have hit : 2≤nbr G v k+nbr G v P := by
        by_contra! small
        have vk : v∉k := fun m => out (front (mem_union_right _ m))
        exact out (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wm,vk⟩,small⟩)))
      rw [Nat.add_comm,←Repair.nbr_add G v dis] at hit
      exact hit.trans (Repair.nbr_mono G v front)
    · by_cases eq : v=M.u
      · subst v; exact u2.trans (Repair.nbr_mono G _ keep)
      by_cases es : v=M.s
      · subst v; exact s2.trans (Repair.nbr_mono G _ keep)
      have vb : v∈M.B := Classical.byContradiction (fun h => wm ((M.outside _).mpr ⟨eq,es,h⟩))
      rw [M.split x y xm ym] at vb
      have xy := (mem_union.mp vb).resolve_left (fun p => out (keep p))
      rcases (show v=x ∨ v=y by simpa using xy) with rfl|rfl
      · have hit : 2≤nbr G v k+nbr G v P := by
          by_contra! small
          exact out (mem_union_right _ (mem_filter.mpr ⟨mem_singleton_self _,small⟩))
        rw [Nat.add_comm,←Repair.nbr_add G v dis] at hit
        exact hit.trans (Repair.nbr_mono G v front)
      · exact y2.trans (Repair.nbr_mono G _ keep)
  have upper : gamma G≤T.card := Nat.sInf_le ⟨_,dom,rfl⟩
  have a := card_union_le P k
  have b := card_union_le (P∪k) (M.failed x y k)
  have c := card_union_le ((P∪k)∪M.failed x y k) (M.extra x y k)
  change P.card≤4 at sz
  change T.card≤_ at c
  omega


private theorem failed_contacts {x y : V} (xm : x∈M.U) (_ym : y∈M.L) {k : Finset V}
    (low : x∈M.extra x y k) :
    nbr G x M.U=1 ∧ nbr G x M.L≤1 ∧ M.L.filter (G.Adj x)⊆{y} := by
  have h := (mem_filter.mp low).2
  rw [M.pin_count] at h
  have one := M.one_U xm
  have xu : (M.U.erase x).filter (G.Adj x)=M.U.filter (G.Adj x) := by
    ext z; simp only [mem_filter,mem_erase]
    exact ⟨fun a => ⟨a.1.2,a.2⟩,fun a => ⟨⟨a.2.ne.symm,a.1⟩,a.2⟩⟩
  have old : nbr G x (M.U.erase x)=nbr G x M.U := congrArg card xu
  have sub : M.L.filter (G.Adj x)⊆{y} := by
    intro z zm; apply mem_singleton.mpr; by_contra ne
    have positive : 0<nbr G x (M.L.erase y) := card_pos.mpr
      ⟨z,mem_filter.mpr ⟨mem_erase.mpr ⟨ne,(mem_filter.mp zm).1⟩,(mem_filter.mp zm).2⟩⟩
    omega
  exact ⟨by omega,(card_le_card sub).trans (card_singleton _).le,sub⟩

private theorem one_fiber (ws : M.W.card=22) {x y : V} (xm : x∈M.U) (ym : y∈M.L) :
    ((M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)).card≤(22-nbr G x M.W).choose 8 := by
  let N := M.W.filter (G.Adj x)
  have sub : (M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)⊆(M.W\N).powersetCard 8 := by
    intro k km
    obtain ⟨ks,hit⟩ := mem_filter.mp km
    obtain ⟨kw,kc⟩ := mem_powersetCard.mp ks
    refine mem_powersetCard.mpr ⟨?_,kc⟩
    intro w wm; apply mem_sdiff.mpr ⟨kw wm,?_⟩; intro wn
    have positive : 0<nbr G x k := card_pos.mpr ⟨w,mem_filter.mpr ⟨wm,(mem_filter.mp wn).2⟩⟩
    have one := (M.retained xm ym).2.2.2.2
    have lo := (mem_filter.mp hit).2
    omega
  have c := card_le_card sub
  rw [card_powersetCard,card_sdiff (show N⊆M.W from filter_subset ..),ws] at c
  exact c

/-- An omitted private neighbor that ever needs repair sees just one other
neighbor of its own cubic. If it sees one neighbor of the other cubic, only
the choice omitting that particular vertex can require a repair. -/
theorem extra_bound (ws : M.W.card=22) {x : V} (xm : x∈M.U) :
    let b := nbr G x M.W
    let j := nbr G x M.L
    let count := ∑ y∈M.L,((M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)).card
    count=0 ∨ (j≤1 ∧ trianglesAt G x≤1+(b+1+j).choose 2 ∧ count≤(3-2*j)*(22-b).choose 8) := by
  classical
  let h (y : V) := (M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)
  change (∑ y∈M.L,(h y).card)=0 ∨ _
  by_cases every : ∀ y∈M.L,(h y).card=0
  · exact Or.inl (sum_eq_zero every)
  push_neg at every
  obtain ⟨y,ym,nonzero⟩ := every
  obtain ⟨k,km⟩ := card_pos.mp (Nat.pos_of_ne_zero nonzero)
  obtain ⟨one,jl,_⟩ := M.failed_contacts xm ym (mem_filter.mp km).2
  have score := M.side_score (T:=M.U) (O:=M.L) rfl rfl M.sep xm M.dis rfl rfl
  rw [one] at score
  refine Or.inr ⟨jl,by simpa only [Nat.add_assoc] using score,?_⟩
  change (∑ y∈M.L,(h y).card)≤_
  by_cases j0 : nbr G x M.L=0
  · have z := sum_le_sum (s:=M.L) (fun y ym => M.one_fiber ws xm ym)
    simpa [h,M.sizes.2,j0] using z
  · have j1 : nbr G x M.L=1 := by omega
    obtain ⟨z,eq⟩ := card_eq_one.mp j1
    have zm : z∈M.L.filter (G.Adj x) := eq ▸ mem_singleton_self _
    have side := (mem_filter.mp zm).1
    have per (v : V) (vm : v∈M.L) : (h v).card ≤ if z=v then (22-nbr G x M.W).choose 8 else 0 := by
      by_cases zv : z=v
      · rw [if_pos zv]; exact M.one_fiber ws xm vm
      · rw [if_neg zv]; apply Nat.le_of_eq; apply card_eq_zero.mpr
        apply eq_empty_of_forall_not_mem; intro k km
        have only := (M.failed_contacts xm vm (mem_filter.mp km).2).2.2
        exact zv (mem_singleton.mp (only zm))
    have zsum := sum_le_sum per
    simpa [j1,side] using zsum

end Graffiti384b.Disjoint30.Board
#print axioms Graffiti384b.Disjoint30.Board.trial
#print axioms Graffiti384b.Disjoint30.Board.extra_bound
