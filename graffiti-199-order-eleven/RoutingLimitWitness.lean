import StarContacts
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open private triangle_absurd from CutTorsoBudget

namespace Graffiti199Depleted.Catalogue.ElevenRoutingWitness

open SimpleGraph

private def row : Fin 11 → ℕ := ![1662,1525,987,53,15,11,1927,326,198,69,67]

/-- Two components of orders three and five separated by the first
three vertices. The five-vertex component cannot span a path by itself. -/
def graph : SimpleGraph (Fin 11) where
  Adj x y := (row x).testBit y.val = true
  symm := by
    change ∀ x y : Fin 11, (row x).testBit y.val = true → (row y).testBit x.val = true
    decide +kernel
  loopless := by
    change ∀ x : Fin 11, ¬ (row x).testBit x.val = true
    decide +kernel

instance adjDecidable : DecidableRel graph.Adj := fun x y =>
  inferInstanceAs (Decidable ((row x).testBit y.val = true))

abbrev ports : Finset (Fin 11) := {0,1,2}
abbrev left : Set (Fin 11) := ↑({3,4,5} : Finset (Fin 11))
abbrev rightFin : Finset (Fin 11) := {6,7,8,9,10}
abbrev right : Set (Fin 11) := ↑rightFin

private def road (D : Finset (Fin 11)) (p : Fin 11) : Prop :=
  p ∈ ports → p ∉ D → ∀ x ∉ D, x = p ∨ graph.Adj x p ∨ ∃ y ∉ D, graph.Adj x y ∧ graph.Adj y p

private instance (D : Finset (Fin 11)) (p : Fin 11) : Decidable (road D p) :=
  inferInstanceAs (Decidable (p ∈ ports → p ∉ D → ∀ x ∉ D,
    x = p ∨ graph.Adj x p ∨ ∃ y ∉ D, graph.Adj x y ∧ graph.Adj y p))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem road_cases (p : Fin 11) :
    road ∅ p ∧ (∀ a : Fin 11, road {a} p) ∧ (∀ a b : Fin 11, road {a,b} p) := by
  fin_cases p <;> decide +kernel

private theorem road_to_port (D : Finset (Fin 11)) (small : D.card < 3) (p : Fin 11) : road D p := by
  have shape : D.card = 0 ∨ D.card = 1 ∨ D.card = 2 := by omega
  rcases shape with zero|one|two
  · rw [Finset.card_eq_zero.mp zero]; exact (road_cases p).1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp one
    exact (road_cases p).2.1 a
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp two
    exact (road_cases p).2.2 a b

theorem connectivity : ConnectivityAtLeast graph 3 := by
  refine ⟨by decide,?_⟩
  intro D small
  obtain ⟨p,hp,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show D.card < ports.card from (show ports.card = 3 by decide).symm ▸ small)
  let h : Survives D := ⟨p,off⟩
  refine @SimpleGraph.Connected.mk _ (DeletionGraph graph D) ?_ ⟨h⟩
  intro x y
  have reach (z : Survives D) : (DeletionGraph graph D).Reachable z h := by
    rcases road_to_port D small p hp off z.val z.property with same|adj|⟨w,hw,zw,wp⟩
    · exact (show z = h from Subtype.ext same) ▸ .rfl
    · exact (show (DeletionGraph graph D).Adj z h from adj).reachable
    · let i : Survives D := ⟨w,hw⟩
      exact (show (DeletionGraph graph D).Adj z i from zw).reachable.trans
        (show (DeletionGraph graph D).Adj i h from wp).reachable
  exact (reach x).trans (reach y).symm

private theorem actual_component {A : Set (Fin 11)} {r : Fin 11}
    (rA : r ∈ A) (off : ∀ v ∈ A, v ∉ ports)
    (boundary : ShoreBoundary graph ports A) (center : ∀ v ∈ A, v ≠ r → graph.Adj r v) :
    componentShore ports ((DeletionGraph graph ports).connectedComponentMk ⟨r,off r rA⟩) = A := by
  let H := DeletionGraph graph ports
  let root : Survives ports := ⟨r,off r rA⟩
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    by_contra outside
    have reach : H.Reachable x root := ConnectedComponent.exact hx
    obtain ⟨w⟩ := reach.symm
    obtain ⟨a,ha,b,hb,ab⟩ :=
      crossingOnWalk (U := {z : Survives ports | z.val ∈ A}) w rA outside
    exact b.property (boundary a.val ha b.val hb ab)
  · intro vA
    let x : Survives ports := ⟨v,off v vA⟩
    by_cases e : v = r
    · have eq : x = root := Subtype.ext e
      exact ⟨x,ConnectedComponent.sound (eq.symm ▸ (show H.Reachable root root from .rfl)),rfl⟩
    · have edge : H.Adj root x := center v vA e
      exact ⟨x,ConnectedComponent.sound edge.reachable.symm,rfl⟩

/-- The witness's deleted graph has exactly the indicated components
of orders three and five. -/
theorem actual_shores :
    ∃ F : LargeCrossingFailure graph, F.cut = ports ∧
      componentShore F.cut F.first = left ∧ componentShore F.cut F.second = right := by
  let C := (DeletionGraph graph ports).connectedComponentMk ⟨3,by decide⟩
  let E := (DeletionGraph graph ports).connectedComponentMk ⟨6,by decide⟩
  have lc : componentShore ports C = left := actual_component (r := 3) (by decide) (by decide)
    (by unfold ShoreBoundary; decide) (by decide)
  have rc : componentShore ports E = right := actual_component (r := 6) (by decide) (by decide)
    (by unfold ShoreBoundary; decide) (by decide)
  have diff : C ≠ E := by
    intro eq
    have r : (3 : Fin 11) ∈ componentShore ports C := lc.symm ▸ (by decide : (3 : Fin 11) ∈ left)
    have l : (3 : Fin 11) ∈ right := rc ▸ (eq ▸ r)
    exact (by decide : (3 : Fin 11) ∉ right) l
  have lSize : 3 ≤ Nat.card (componentShore ports C) := by
    rw [lc,Nat.card_eq_fintype_card]
    decide
  have rSize : 3 ≤ Nat.card (componentShore ports E) := by
    rw [rc,Nat.card_eq_fintype_card]
    decide
  exact ⟨⟨ports,by decide,C,E,diff,lSize,rSize⟩,rfl,lc,rc⟩

theorem no_crossing : ¬ CrossingBetweenSurvivingEdges graph := by
  intro cross
  have banned : ∀ x y : Fin 11, x ∈ left → y ∉ left → y ∉ ports → ¬ graph.Adj x y := by
    decide +kernel
  obtain ⟨x,xA,y,yA,_,yD,xy⟩ := cross ports (by decide) left
    ⟨3,by decide,4,by decide,by decide,by decide,by decide⟩
    ⟨6,by decide,7,by decide,by decide,by decide,by decide⟩
  exact banned x y xA yA yD xy

theorem exact_connectivity : vertexConnectivity graph = 3 := by
  classical
  have ge : 3 ≤ vertexConnectivity graph := by
    unfold vertexConnectivity
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by decide),connectivity⟩)
  have le : vertexConnectivity graph ≤ 3 := by
    by_contra! h
    apply no_crossing
    apply edgeReach_iff_crossing_between_surviving_edges.mp
    intro D small a _ c _ _ _
    exact ((connectivityAtLeast_vertexConnectivity (G := graph)).2 D (by omega)).preconnected a c
  omega

private def Triangle (S : Finset (Fin 11)) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, graph.Adj a b ∧ graph.Adj a c ∧ graph.Adj c b
private def Separates (S U : Finset (Fin 11)) : Prop :=
  (∃ a ∈ S, a ∈ U) ∧ (∃ b ∈ S, b ∉ U) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ∈ U → b ∉ U → ¬ graph.Adj a b

private instance (S : Finset (Fin 11)) : Decidable (Triangle S) :=
  inferInstanceAs (Decidable (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, graph.Adj a b ∧ graph.Adj a c ∧ graph.Adj c b))
private instance (S U : Finset (Fin 11)) : Decidable (Separates S U) :=
  inferInstanceAs (Decidable ((∃ a ∈ S, a ∈ U) ∧ (∃ b ∈ S, b ∉ U) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ∈ U → b ∉ U → ¬ graph.Adj a b))

private def degreeMass (S : Finset (Fin 11)) : ℕ :=
  ∑ v ∈ S, (S.filter (graph.Adj v)).card

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem large_set_certificate :
    ∀ S : Finset (Fin 11), 6 ≤ S.card →
      degreeMass S ≠ 2 * (S.card - 1) ∨ Triangle S ∨ Separates S {9} := by
  decide +kernel

private theorem mass_of_tree (S : Finset (Fin 11))
    (tree : (graph.induce (↑S : Set (Fin 11))).IsTree) :
    degreeMass S = 2 * (S.card - 1) := by
  classical
  let H := graph.induce (↑S : Set (Fin 11))
  have counts (v : (↑S : Set (Fin 11))) : H.degree v = (S.filter (graph.Adj v.val)).card := by
    let inclusion : (↑S : Set (Fin 11)) ↪ Fin 11 := ⟨Subtype.val,Subtype.val_injective⟩
    have same : (H.neighborFinset v).map inclusion = S.filter (graph.Adj v.val) := by
      ext x
      constructor
      · intro h
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
        exact Finset.mem_filter.mpr ⟨y.property,(H.mem_neighborFinset _ _).mp hy⟩
      · intro h
        obtain ⟨hx,adj⟩ := Finset.mem_filter.mp h
        exact Finset.mem_map.mpr ⟨⟨x,hx⟩,(H.mem_neighborFinset _ _).mpr adj,rfl⟩
    rw [← H.card_neighborFinset_eq_degree,← same,Finset.card_map]
  have double := H.sum_degrees_eq_twice_card_edges
  have summed : (∑ v : (↑S : Set (Fin 11)), H.degree v) = degreeMass S := by
    simp only [counts,degreeMass]
    rw [← Finset.sum_attach S (fun v => (S.filter (graph.Adj v)).card)]
    rfl
  rw [summed] at double
  have e := (SimpleGraph.isTree_iff_connected_and_card.mp tree).2
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,
    ← H.edgeFinset_card] at e
  change H.edgeFinset.card + 1 = Fintype.card (↥S) at e
  rw [Fintype.card_coe] at e
  omega

private theorem cut_absurd {S U : Finset (Fin 11)} (T : (graph.induce (↑S : Set (Fin 11))).IsTree)
    (h : Separates S U) : False := by
  obtain ⟨⟨a,ha,au⟩,⟨b,hb,bu⟩,ban⟩ := h
  let A : Set (↑S : Set (Fin 11)) := {x | x.val ∈ U}
  obtain ⟨w⟩ := T.isConnected.preconnected ⟨a,ha⟩ ⟨b,hb⟩
  obtain ⟨x,hx,y,hy,xy⟩ := crossingOnWalk (U := A) w au bu
  exact ban x.val x.property y.val y.property hx hy xy

theorem budget : treeNumber graph ≤ 5 := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro S h
  change S.card ≤ 5
  by_contra! large
  let H := graph.induce (↑S : Set (Fin 11))
  have tree : H.IsTree := (Finset.mem_filter.mp h).2
  rcases large_set_certificate S (by omega) with mismatch|tri|cut
  · exact mismatch (mass_of_tree S tree)
  · obtain ⟨a,aS,b,bS,c,cS,ab,ac,cb⟩ := tri
    exact triangle_absurd tree (show H.Adj ⟨a,aS⟩ ⟨b,bS⟩ from ab)
      (show H.Adj ⟨a,aS⟩ ⟨c,cS⟩ from ac) (show H.Adj ⟨c,cS⟩ ⟨b,bS⟩ from cb)
  · exact cut_absurd tree cut

theorem high_cut : ∀ v ∈ ports, 4 ≤ graph.degree v := by decide +kernel

theorem cubics : ∀ v : Fin 11, graph.degree v = 3 ↔ v = 5 ∨ v = 9 ∨ v = 10 := by decide +kernel

theorem independent_cubics :
    ∀ a b, graph.degree a = 3 → graph.degree b = 3 → ¬ graph.Adj a b := by decide +kernel

theorem independent_five :
    ∀ u ∈ ({4,5,7,9,10} : Finset (Fin 11)), ∀ v ∈ ({4,5,7,9,10} : Finset (Fin 11)),
      ¬ graph.Adj u v := by decide +kernel

theorem induced_claw :
    graph.Adj 0 1 ∧ graph.Adj 0 3 ∧ graph.Adj 0 9 ∧
    ¬ graph.Adj 1 3 ∧ ¬ graph.Adj 1 9 ∧ ¬ graph.Adj 3 9 := by decide +kernel

private theorem list_of_length_five {W : Type*} {L : List W} (len : L.length = 5) :
    ∃ a b c d e, L = [a,b,c,d,e] := by
  obtain ⟨a,L₁,rfl⟩ := List.length_pos_iff_exists_cons.mp (show 0 < L.length by omega)
  simp only [List.length_cons] at len
  obtain ⟨b,L₂,rfl⟩ := List.length_pos_iff_exists_cons.mp (show 0 < L₁.length by omega)
  simp only [List.length_cons] at len
  obtain ⟨c,L₃,rfl⟩ := List.length_pos_iff_exists_cons.mp (show 0 < L₂.length by omega)
  simp only [List.length_cons] at len
  obtain ⟨d,L₄,rfl⟩ := List.length_pos_iff_exists_cons.mp (show 0 < L₃.length by omega)
  simp only [List.length_cons] at len
  obtain ⟨e,rest,rfl⟩ := List.length_pos_iff_exists_cons.mp (show 0 < L₄.length by omega)
  simp only [List.length_cons] at len
  have nil : rest = [] := List.length_eq_zero_iff.mp (by omega)
  exact ⟨a,b,c,d,e,by rw [nil]⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem right_list_certificate :
    ∀ a b c d e : ↥rightFin, ¬ (([a.val,b.val,c.val,d.val,e.val] : List (Fin 11)).Nodup ∧
      ([a.val,b.val,c.val,d.val,e.val] : List (Fin 11)).Chain' graph.Adj) := by
  decide +kernel

/-- The five-vertex component has no spanning path at any endpoints. -/
theorem no_spanning_path_on_right : ¬ Nonempty (PathOn graph right) := by
  rintro ⟨P⟩
  have eq : P.vertices.toFinset = rightFin := by
    ext v
    rw [List.mem_toFinset,P.covers]
    rfl
  have len : P.vertices.length = 5 := by
    rw [← List.toFinset_card_of_nodup P.nodup,eq]
    decide
  obtain ⟨a,b,c,d,e,form⟩ := list_of_length_five len
  have covers (x : Fin 11) (hx : x ∈ [a,b,c,d,e]) : x ∈ rightFin :=
    (P.covers _).mp (form.symm ▸ hx)
  have nd := P.nodup
  have ch := P.chain
  rw [form] at nd ch
  exact right_list_certificate ⟨a,covers _ (by simp)⟩ ⟨b,covers _ (by simp)⟩
    ⟨c,covers _ (by simp)⟩ ⟨d,covers _ (by simp)⟩ ⟨e,covers _ (by simp)⟩ ⟨nd,ch⟩

/-- Every Hamiltonian path of the whole graph must split its five-vertex
side into at least two intervals. -/
theorem no_one_interval_on_right (P : PathOn graph Set.univ) :
    ¬ ∃ L M R : List (Fin 11), P.vertices = L ++ M ++ R ∧
      (∀ v, v ∈ M ↔ v ∈ right) := by
  rintro ⟨L,M,R,h,cov⟩
  have nonempty : M ≠ [] := fun e => List.not_mem_nil (e ▸ (cov 6).mpr (by decide))
  have chain := P.chain
  have nd := P.nodup
  rw [h] at chain nd
  exact no_spanning_path_on_right
    ⟨⟨M,nonempty,chain.left_of_append.right_of_append,
      (List.nodup_append.mp (List.nodup_append.mp nd).1).2.1,cov⟩⟩

theorem traceable : Traceable graph := by
  apply traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  refine ⟨⟨[0,4,3,5,1,7,8,2,9,6,10],by simp,by decide,by decide,?_⟩⟩
  intro v
  change v ∈ ([0,4,3,5,1,7,8,2,9,6,10] : List (Fin 11)) ↔ True
  fin_cases v <;> decide

#print axioms actual_shores
#print axioms exact_connectivity
#print axioms no_crossing
#print axioms budget
#print axioms high_cut
#print axioms independent_cubics
#print axioms independent_five
#print axioms induced_claw
#print axioms no_spanning_path_on_right
#print axioms no_one_interval_on_right
#print axioms traceable

end Graffiti199Depleted.Catalogue.ElevenRoutingWitness
