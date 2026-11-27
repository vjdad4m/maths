import ReplicaGirthGap
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Finset SimpleGraph
namespace KelmansCactus.NearPerfectReplica.Layout
noncomputable section
variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
variable {A : SimpleGraph U} {B : SimpleGraph J} {r : U}
variable (L : Layout A B r)

/-- An oriented boundary in which each undirected crossing edge
is represented just once, with the first endpoint in the shore. -/
def cutEdges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : Finset (V×V) :=
  univ.filter (fun p=>p.1∈S ∧ p.2∉S ∧ G.Adj p.1 p.2)

theorem three_cell_seams (i : J) : (cutEdges L.graph (cell i)).card=3 := by
  classical
  let e : Fin 3→Host J r×Host J r := fun j=>(L.p (i,j),L.q (i,j))
  have inj : Function.Injective e := by
    intro j k ejk
    have q : L.p (i,j)=L.p (i,k) := congrArg (fun v : Host J r×Host J r=>v.1) ejk
    exact congrArg (fun v : J×Fin 3=>v.2) (L.p_inj q)
  have eq : cutEdges L.graph (cell i)=(univ:Finset (Fin 3)).image e := by
    ext z
    obtain ⟨z1,z2⟩ := z
    simp only [cutEdges,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨hit,out,adj⟩
      obtain ⟨j,ej1,ej2⟩ := ((L.cell_seam i).edge _ hit _ out).mp adj
      exact mem_image.mpr ⟨j,mem_univ _,Prod.ext ej1 ej2⟩
    · intro m
      obtain ⟨j,_,ej⟩ := mem_image.mp m
      have p1 : L.p (i,j)=z1 := congrArg (fun v : Host J r×Host J r=>v.1) ej
      have p2 : L.q (i,j)=z2 := congrArg (fun v : Host J r×Host J r=>v.2) ej
      rw [←p1,←p2]
      exact ⟨(L.cell_seam i).left j,(L.cell_seam i).right j,L.edge_at_slot (i,j)⟩
  rw [eq,card_image_of_injective _ inj,card_univ,Fintype.card_fin]

local instance [DecidableRel A.Adj] : DecidableRel (rootDeleted (A:=A) (r:=r)).Adj :=
  fun x y=>inferInstanceAs (Decidable (A.Adj x.val y.val))

omit [Fintype J] [DecidableEq J] in
private theorem root_deleted_degree_at_least_two [DecidableRel A.Adj]
    (cub : ∀ v,A.degree v=3) (x : Cell r) :
    2≤(rootDeleted (A:=A) (r:=r)).degree x := by
  classical
  let F := (A.neighborFinset x.val).erase r
  have lower : 2≤F.card := by
    by_cases h : r∈A.neighborFinset x.val
    · dsimp [F]
      rw [card_erase_of_mem h,card_neighborFinset_eq_degree,cub]
    · dsimp [F]
      rw [erase_eq_of_not_mem h,card_neighborFinset_eq_degree,cub]
      decide
  let f : ↥F → (rootDeleted (A:=A) (r:=r)).neighborSet x := fun y=>
    ⟨⟨y.val,(mem_erase.mp y.property).1⟩,
      (mem_neighborFinset A x.val y.val).mp (mem_erase.mp y.property).2⟩
  have fi : Function.Injective f := by
    intro x y e
    exact Subtype.ext (congrArg (fun v : (rootDeleted (A:=A) (r:=r)).neighborSet _=>v.val.val) e)
  have b := Fintype.card_le_of_injective f fi
  rw [Fintype.card_coe,card_neighborSet_eq_degree] at b
  exact lower.trans b

omit [Fintype J] [DecidableEq J] in
theorem root_deleted_has_cycle [DecidableRel A.Adj]
    (cub : ∀ v,A.degree v=3) (con : KelmansStarter.ThreeConnected A) :
    ¬(rootDeleted (A:=A) (r:=r)).IsAcyclic := by
  let R := rootDeleted (A:=A) (r:=r)
  have conn : R.Connected := by
    unfold R rootDeleted
    have eql : ({x : U | x∉({r} : Finset U)} : Set U) = {x|x≠r} := by ext; simp
    exact Eq.mp (congrArg (fun S : Set U=>(A.induce S).Connected) eql)
      (con.2 {r} (by simp))
  intro forest
  have tree : R.IsTree := ⟨conn,forest⟩
  have eq := tree.card_edgeFinset
  have sum := R.sum_degrees_eq_twice_card_edges
  have lower : (∑ _ : Cell r, 2) ≤ ∑ v : Cell r,R.degree v :=
    sum_le_sum (fun v _=>root_deleted_degree_at_least_two cub v)
  have tally : (∑ _ : Cell r, (2:ℕ)) = Fintype.card (Cell r)*2 := by simp
  rw [tally,sum] at lower
  omega

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
private theorem cell_inherits_cycle
    (cycle : ¬(rootDeleted (A:=A) (r:=r)).IsAcyclic)
    (T : Set (Host J r)) (i : J) (all : ∀ u : Cell r,(i,u)∈T) :
    ¬(L.graph.induce T).IsAcyclic := by
  classical
  let R := rootDeleted (A:=A) (r:=r)
  let f : R→g L.graph.induce T :=
    ⟨fun u=>⟨(i,u),all u⟩,fun h=>Or.inl ⟨rfl,h⟩⟩
  have fi : Function.Injective f := by
    intro a b e
    exact congrArg (fun v : T=>v.val.2) e
  intro no
  apply cycle
  intro u c cyc
  exact no (c.map f) (cyc.map fi)

/-- The repeated three-port substitution cannot enter the cyclically
4-edge-connected class: every cell boundary is an exact three-edge
cut, and both sides retain a cycle. -/
theorem genuine_cyclic_three_cut [DecidableRel A.Adj] (cub : ∀ v,A.degree v=3)
    (con : KelmansStarter.ThreeConnected A) (i : J) (other : ∃ j : J,j≠i) :
    (cutEdges L.graph (cell i)).card=3 ∧
      ¬(L.graph.induce (↑(cell (r:=r) i) : Set (Host J r))).IsAcyclic ∧
      ¬(L.graph.induce {v | v∉cell i}).IsAcyclic := by
  obtain ⟨j,ji⟩ := other
  have localCycle := root_deleted_has_cycle (r:=r) cub con
  exact ⟨L.three_cell_seams i,L.cell_inherits_cycle localCycle _ i (fun _=>mem_cell.mpr rfl),
    L.cell_inherits_cycle localCycle _ j (fun _ h=>ji (mem_cell.mp h))⟩

#print axioms genuine_cyclic_three_cut
end
end KelmansCactus.NearPerfectReplica.Layout
