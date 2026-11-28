import AdjacentCutFiveTwoTwinRoute189
import AdjacentCutFiveTwoOrderTwenty189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_hit_a from AdjacentCutFiveActual189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private positive_cap from AdjacentCutFiveComponents189
open private mem_positive from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000


theorem traceable_of_order_seventeen_adjacent_twin_two_cut
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z ≠ a → z ≠ b → (G.Adj a z ↔ G.Adj b z))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (two : Nat.card (CutGraph (G:=G) a b).ConnectedComponent = 2)
    (n : 17 ≤ Fintype.card V) :
    ∃ s t, ∃ p : G.Walk s t, p.IsPath ∧ ∀ z, z∈p.support := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  have dis := shore_disjoint cd
  have sub : (univ.erase a |>.erase b : Finset V) ⊆ Shore C ∪ Shore D := by
    intro z hz
    exact mem_union.mpr (cover (mem_erase.mp (mem_erase.mp hz).2).1
      (mem_erase.mp hz).1)
  have sz := card_le_card sub
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),
    card_univ,card_union_of_disjoint dis] at sz
  have part (K : (CutGraph (G := G) a b).ConnectedComponent) : (AdjTwinOdd K).card + (AdjTwinEven K).card = (Shore K).card := by
    have dis : Disjoint (AdjTwinOdd K) (AdjTwinEven K) :=
      disjoint_left.mpr (fun _ ho he => (mem_filter.mp ho).2 (mem_filter.mp he).2)
    rw [←card_union_of_disjoint dis]
    congr 1
    ext z
    simp only [AdjTwinOdd,AdjTwinEven,mem_union,mem_filter]
    constructor
    · exact fun h=>h.elim And.left And.left
    intro hz
    by_cases e : Even (G.dist a z)
    · exact .inr ⟨hz,e⟩
    · exact .inl ⟨hz,e⟩
  have esub : AdjTwinEven C ∪ AdjTwinEven D ⊆ PositiveEven G a := by
    have sub (K : (CutGraph (G := G) a b).ConnectedComponent) : AdjTwinEven K ⊆ PositiveEven G a := by
      intro z hz
      obtain ⟨zk,ze⟩ := mem_filter.mp hz
      exact mem_positive.mpr ⟨fun e => (shore_off K).1 (e ▸ zk),ze⟩
    exact union_subset (sub C) (sub D)
  have edis := dis.mono (show AdjTwinEven C ⊆ Shore C from filter_subset _ _)
    (show AdjTwinEven D ⊆ Shore D from filter_subset _ _)
  have ev := (card_le_card esub).trans (positive_cap a even)
  rw [card_union_of_disjoint edis] at ev
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab.ne conn C
  obtain ⟨y,yd,ay⟩ := shore_hit_a ab.ne conn D
  have co := (card_le_card (adj_twin_odd_foreign hc twin cd.symm yd ay)).trans (positive_cap y even)
  have do' := (card_le_card (adj_twin_odd_foreign hc twin cd xc ax)).trans (positive_cap x even)
  have cp := part C
  have dp := part D
  obtain ⟨s,t,as',p⟩ := adj_twin_route_of_balanced_saturated hc ab.ne even twin conn cd
    (by omega) (by omega) (by omega)
  obtain ⟨u,v,au,q⟩ := adj_twin_route_of_balanced_saturated hc ab.ne even twin conn cd.symm
    (by omega) (by omega) (by omega)
  have uD : u∈Shore D := by
    obtain ⟨w,_,hs⟩ := q
    exact (hs u).mp w.start_mem_support
  have ub : u≠b := fun h=>(shore_off D).2 (h ▸ uD)
  have bu := (twin u au.ne.symm ub).mp au
  have left := p.reverse.suffix as'.symm (shore_off C).1
  have right := q.prefix bu (shore_off D).2
  have apart : Disjoint (insert a (Shore C)) (insert b (Shore D)) := by
    refine disjoint_left.mpr ?_
    intro z zl zr
    rcases mem_insert.mp zl with rfl|zc
    · exact (by simp [ab.ne,(shore_off D).1] : z∉insert b (Shore D)) zr
    rcases mem_insert.mp zr with rfl|zd
    · exact (shore_off C).2 zc
    · exact disjoint_left.mp dis zc zd
  obtain ⟨w,wp,ws⟩ := left.join right apart ab
  refine ⟨t,v,w,wp,fun z => (ws z).mpr ?_⟩
  by_cases za : z=a
  · simp [za]
  by_cases zb : z=b
  · simp [zb]
  rcases cover za zb with h|h <;> simp [h]

#print axioms traceable_of_order_seventeen_adjacent_twin_two_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
