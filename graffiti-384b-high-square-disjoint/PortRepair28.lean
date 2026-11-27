import PortGeometry28

namespace Graffiti384b.Port28.Board
open Finset SimpleGraph
open private ForcedCubics.third_contact from SharedSaving33
open private Repair.nbr_add Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Board G)

def extra (x y : V) (k : Finset V) :=
  ({x}:Finset V).filter (fun w => nbr G w k+nbr G w (M.pins x y)<2)

def failed (x y : V) (k : Finset V) := PortFibers28.failures G M.W k (fun v => nbr G v (M.pins x y))

private theorem retained {x y : V} (xm : x∈M.U) (ym : y∈M.L) :
    (M.pins x y).card≤3 ∧ 2≤nbr G M.u (M.pins x y) ∧ 2≤nbr G M.s (M.pins x y) ∧
      2≤nbr G y (M.pins x y) ∧ 1≤nbr G x (M.pins x y) := by
  classical
  let P := M.pins x y
  have cP : M.c∈P := mem_union_left _ (mem_union_left _ (mem_singleton_self _))
  have ux := (G.mem_neighborFinset ..).mp (mem_erase.mp xm).2
  have sy := (G.mem_neighborFinset ..).mp (mem_erase.mp ym).2
  have X : (M.U.erase x).card=1 := by rw [card_erase_of_mem xm,M.sizes.1]
  have Y : (M.L.erase y).card=1 := by rw [card_erase_of_mem ym,M.sizes.2]
  obtain ⟨p,pm⟩ := card_pos.mp (show 0<(M.U.erase x).card by omega)
  obtain ⟨q,qm⟩ := card_pos.mp (show 0<(M.L.erase y).card by omega)
  have pP : p∈P := mem_union_left _ (mem_union_right _ pm)
  have qP : q∈P := mem_union_right _ qm
  have pc := (mem_erase.mp (mem_erase.mp pm).2).1
  have qc := (mem_erase.mp (mem_erase.mp qm).2).1
  have up := (G.mem_neighborFinset ..).mp (mem_erase.mp (mem_erase.mp pm).2).2
  have sq := (G.mem_neighborFinset ..).mp (mem_erase.mp (mem_erase.mp qm).2).2
  obtain ⟨uc,sc⟩ := M.contacts
  have sz := card_union_le (({M.c}:Finset V)∪M.U.erase x) (M.L.erase y)
  have fs := card_union_le ({M.c}:Finset V) (M.U.erase x)
  rw [card_singleton] at fs
  change P.card≤_ at sz
  refine ⟨by change P.card≤3; omega,PinnedColor34.two G pc up uc pP cP,
    PinnedColor34.two G qc sq sc qP cP,?_,?_⟩
  · exact PinnedColor34.two G qc (EarAnchor.full_neighbors G M.ds M.ss sy sq (mem_erase.mp qm).1.symm)
      (EarAnchor.full_neighbors G M.ds M.ss sy sc (mem_erase.mp ym).1) qP cP
  · rcases ForcedCubics.third_contact G M.du M.su.ge pc up uc ux (mem_erase.mp pm).1.symm (mem_erase.mp xm).1 with edge|edge
    · exact card_pos.mpr ⟨p,mem_filter.mpr ⟨pP,edge⟩⟩
    · exact card_pos.mpr ⟨M.c,mem_filter.mpr ⟨cP,edge⟩⟩

/-- Any particular sample extends to a 2-dominating set by the indicated repairs. -/
theorem trial {x y : V} (xm : x∈M.U) (ym : y∈M.L) {k : Finset V} (km : k∈M.W.powersetCard 8) :
    gamma G≤11+(M.failed x y k).card+(M.extra x y k).card := by
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
  change P.card≤3 at sz
  change T.card≤_ at c
  omega

private theorem degree_at_failure {x y : V} (xm : x∈M.U) (ym : y∈M.L) {k : Finset V}
    (sm : x∈M.extra x y k) :
    G.degree x≤nbr G x M.W+3 := by
  classical
  have low := (mem_filter.mp sm).2
  have xp : ¬G.Adj x M.s := fun e => disjoint_left.mp M.dis xm (mem_erase.mpr
    ⟨(mem_erase.mp xm).1,(G.mem_neighborFinset ..).mpr e.symm⟩)
  let P := M.pins x y
  have sub : G.neighborFinset x⊆((M.W.filter (G.Adj x))∪P.filter (G.Adj x))∪{M.u,y} := by
    intro z zm
    have edge := (G.mem_neighborFinset ..).mp zm
    by_cases zw : z∈M.W
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zw,edge⟩))
    by_cases zu : z=M.u
    · exact mem_union_right _ (mem_insert.mpr (Or.inl zu))
    have zs : z≠M.s := fun eq => xp (eq ▸ edge)
    have zb : z∈M.B := Classical.byContradiction (fun h => zw ((M.outside _).mpr ⟨zu,zs,h⟩))
    rw [M.split x y xm ym] at zb
    rcases mem_union.mp zb with p|two
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨p,edge⟩))
    · have zy := (mem_insert.mp two).resolve_left edge.ne.symm
      exact mem_union_right _ (mem_insert_of_mem zy)
  have a := (card_le_card sub).trans (card_union_le ..)
  have b := card_union_le (M.W.filter (G.Adj x)) (P.filter (G.Adj x))
  have c := card_insert_le M.u ({y}:Finset V)
  rw [card_singleton] at c
  rw [card_neighborFinset_eq_degree] at a
  change _≤nbr G x M.W+nbr G x P at b
  change nbr G x k+nbr G x P<2 at low
  omega

/-- The omitted private neighbor of the score-two cubic already has one
pin. A deficiency requires that the sample miss all its exterior neighbors. -/
theorem extra_fiber (ws : M.W.card=21) {x : V} (xm : x∈M.U) :
    let b := nbr G x M.W
    (∑ y∈M.L,((M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)).card)≤
      if G.degree x≤b+3 then 2*(21-b).choose 8 else 0 := by
  classical
  dsimp only
  by_cases h : G.degree x≤nbr G x M.W+3
  · rw [if_pos h]
    have each (y : V) (ym : y∈M.L) :
        ((M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)).card≤(21-nbr G x M.W).choose 8 := by
      let N := M.W.filter (G.Adj x)
      have sub : (M.W.powersetCard 8).filter (fun k => x∈M.extra x y k)⊆(M.W\N).powersetCard 8 := by
        intro k km
        obtain ⟨ks,hit⟩ := mem_filter.mp km
        obtain ⟨kw,kc⟩ := mem_powersetCard.mp ks
        refine mem_powersetCard.mpr ⟨?_,kc⟩
        intro w wm
        apply mem_sdiff.mpr ⟨kw wm,?_⟩
        intro wn
        have positive : 0<nbr G x k := card_pos.mpr ⟨w,mem_filter.mpr ⟨wm,(mem_filter.mp wn).2⟩⟩
        have one := (M.retained xm ym).2.2.2.2
        have low := (mem_filter.mp hit).2
        omega
      have c := card_le_card sub
      rw [card_powersetCard,card_sdiff (show N⊆M.W from filter_subset ..),ws] at c
      exact c
    have z := sum_le_sum each
    simpa [M.sizes.2] using z
  · rw [if_neg h]
    exact Nat.le_of_eq (sum_eq_zero (fun y ym => card_eq_zero.mpr (filter_eq_empty_iff.mpr
      (fun k _ sm => h (M.degree_at_failure xm ym sm)))))

end Graffiti384b.Port28.Board
#print axioms Graffiti384b.Port28.Board.trial
#print axioms Graffiti384b.Port28.Board.extra_fiber
