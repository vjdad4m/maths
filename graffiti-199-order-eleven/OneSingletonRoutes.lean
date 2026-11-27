import StarContacts

open private no_third_port_of_two_paths_with_singleton from OrderTenSingleton
open private exists_third_port from ThreePathWithRoute
open private ThreeVertexShore.reversed ThreeVertexShore.left_two ThreeVertexShore.right_two
  two_present_ports from TwoShortShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V} {r : V}

set_option maxHeartbeats 800000 in
/-- A three-vertex path, a routable opposite side, and a singleton can
be traversed across a three-cut. If compatibility fails, the path
component is used in two pieces. -/
theorem traceable_of_three_path_and_opposite_route_with_singleton
    (S : ThreeVertexShore G A) (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (apart : Disjoint A B)
    (hr : CutSingleton G D r) (rA : r ∉ A) (rB : r ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r)
    {p q : V} (pD : p ∈ D) (qD : q ∈ D) (pq : p ≠ q) (R : ShoreRoute G B p q) :
    Traceable G := by
  classical
  by_contra no
  obtain ⟨t,pt,qt,frame⟩ := exists_third_port (D := D) size pD qD pq
  subst D
  have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ ({p,q,t} : Finset V) ∨ v = r := by
    have h := cover v
    tauto
  have forbid := no_third_port_of_two_paths_with_singleton conn no pq pt qt rB rA hr.1
    ((hr.2 p).mpr pD) ((hr.2 q).mpr qD) offB offA boundA apart.symm swap R
  have zl := two_present_ports pq (ThreeVertexShore.left_two S conn boundA) (forbid S)
  have missR : ¬ G.Adj t S.right := forbid (ThreeVertexShore.reversed S)
  have zr := two_present_ports pq (ThreeVertexShore.right_two S conn boundA) missR
  obtain ⟨y,hy,ty⟩ := contact_of_shore conn (by omega) offA boundA ⟨S.left,S.left_mem⟩
    (p := t) (by simp)
  have y' : y ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ hy
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at y'
  have tm : G.Adj t S.middle := by
    rcases y' with e|e|e
    · exact (forbid S (e ▸ ty)).elim
    · exact e ▸ ty
    · exact (missR (e ▸ ty)).elim
  let front := [r,t,p,q]
  let inner := [S.middle,S.left,S.right]
  have memFront (v : V) : v ∈ front ↔ v = r ∨ v ∈ ({p,q,t} : Finset V) := by
    simp only [front,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton]
    simp only [or_comm,or_left_comm,or_assoc]
  have memInner (v : V) : v ∈ inner ↔ v ∈ A := by
    have eq : v ∈ A ↔ v ∈ ({S.left,S.middle,S.right} : Set V) :=
      Iff.of_eq (congrArg (fun U : Set V => v ∈ U) S.shape)
    rw [eq]
    simp only [inner,List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]
    simp only [or_comm,or_left_comm,or_assoc]
  have nd : (front ++ inner).Nodup := by
    have rp : r ≠ p := fun e => hr.1 (by simp [e])
    have rq : r ≠ q := fun e => hr.1 (by simp [e])
    have rt : r ≠ t := fun e => hr.1 (by simp [e])
    refine List.nodup_append.mpr ⟨by simp [front,rp,rq,rt,pq,pt.symm,qt.symm],
      by simp [inner,S.lm.ne.symm,S.lr,S.mr.ne],?_⟩
    intro v hf hi
    rcases (memFront v).mp hf with e|hd
    · exact rA (e ▸ (memInner v).mp hi)
    · exact offA v hd ((memInner v).mp hi)
  let f : Fin 7 → V := ![r,t,p,q,S.middle,S.left,S.right]
  have perm : ([r,t,S.middle,S.left,p] ++ [q,S.right]).Perm (front ++ inner) :=
    (show ([0,1,4,5,2,3,6] : List (Fin 7)).Perm [0,1,2,3,4,5,6] by decide).map f
  have coverage (v : V) : v ∈ [r,t,S.middle,S.left,p] ++ [q,S.right] ↔ v ∉ B := by
    rw [perm.mem_iff,List.mem_append,memFront,memInner]
    constructor
    · rintro ((e|d)|a)
      · exact e.symm ▸ rB
      · exact offB _ d
      · exact Set.disjoint_left.mp apart a
    · intro nv
      rcases cover v with a|b|d|e
      · exact Or.inr a
      · exact (nv b).elim
      · exact Or.inl (Or.inr d)
      · exact Or.inl (Or.inl e)
  have rt : G.Adj r t := (hr.2 t).mpr (by simp)
  exact no (traceable_of_route_between_lists (L := [r,t,S.middle,S.left,p]) (R := [q,S.right])
    R (by simp [List.chain'_cons,rt,tm,S.lm.symm,zl.1.symm])
    (List.chain'_pair.mpr zr.2) (by simp) (by simp)
    ((List.Perm.nodup_iff perm).mpr nd) coverage)

#print axioms traceable_of_three_path_and_opposite_route_with_singleton

end Graffiti199Depleted.Catalogue
