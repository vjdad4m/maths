import NearPerfectSharpGraph
import FourReplace

open Finset
namespace KelmansCactus.NearPerfectCommonCap
open ThreePort Substitute PathSlides ContactSlides NearPerfectSharpGraph

variable {V U J : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
  [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : SimpleGraph U}

/-- A proposed near-perfect packing on any sufficiently large three-port
replication forces the common original cap to have a full factor. The
seam and exact-copy hypotheses are separated from the graph construction. -/
theorem few_holes_on_replica_forces_original_factor {P : Parts V}
    (ok : PackIn G univ P)
    (root : U) (neigh : Fin 3→U) (isNeigh : ∀ j,B.Adj root (neigh j))
    (residue : Fintype.card U%3=0)
    (e : J→(U↪V))
    (D : J→Finset V) (copy : ∀ i,D i=(univ.erase root).map (e i))
    (sep : (↑(univ:Finset J):Set J).PairwiseDisjoint D)
    (p q : J×Fin 3→V) (ports : ∀ i j,p (i,j)=e i (neigh j))
    (mate : J×Fin 3→J×Fin 3) (pair : Function.Involutive mate)
    (mirror : ∀ s,p (mate s)=q s)
    (seams : ∀ i, Seam (G:=G) (D i) (fun j=>p (i,j)) (fun j=>q (i,j)))
    (kept : ∀ i, ∀ x∈D i, ∀ y∈D i, G.Adj x y → ((B.map (e i))).Adj x y)
    (budget : 2*((univ:Finset V)\P.biUnion id).card < Fintype.card J) :
    KelmansStarter.HasP3Factor B := by
  classical
  by_contra no
  let K : J→SimpleGraph V := fun i=>B.map (e i)
  let r : J→V := fun i=>e i root
  have rr (i : J) : r i∉D i := by
    intro hr
    rw [copy] at hr
    obtain ⟨u,hu,same⟩ := mem_map.mp hr
    exact (mem_erase.mp hu).1 ((e i).injective same)
  have cap (i : J) (j : Fin 3) : (K i).Adj (r i) (p (i,j)) := by
    rw [ports]
    exact SimpleGraph.map_adj_apply.mpr (isNeigh j)
  have modCell (i : J) : (D i).card%3=2 := by
    rw [copy,card_map,card_erase_of_mem (mem_univ root),card_univ]
    have pos : 0<Fintype.card U := Fintype.card_pos_iff.mpr ⟨root⟩
    omega
  have bad (i : J) : ¬Closed (K i) (insert (r i) (D i)) := by
    intro h
    have eq : insert (r i) (D i) = (univ:Finset U).map (e i) := by
      rw [copy,← map_insert,insert_erase (mem_univ root)]
    rw [eq] at h
    exact no (FourReplace.full_factor_of_closed_image (e i)
      (fun _ _ adj=>SimpleGraph.map_adj_apply.mp adj) h)
  exact (Nat.not_le_of_gt budget)
    (bad_caps_force_half_vacancies ok D sep p q mate pair mirror seams modCell K r rr kept cap bad)

#print axioms few_holes_on_replica_forces_original_factor
end KelmansCactus.NearPerfectCommonCap
