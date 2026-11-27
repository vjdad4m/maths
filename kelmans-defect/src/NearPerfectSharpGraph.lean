import NearPerfectSharp

open Finset
namespace KelmansCactus.NearPerfectSharpGraph
open ThreePort Substitute PathSlides ContactSlides NearPerfectCells NearPerfectSharp

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V}

/-- The exact paired endpoint scores double the earlier capacity-only
lower bound: bad three-port caps force at least one actual vacancy
for every two replica cells, uniformly over all partial packings. -/
theorem bad_caps_force_half_vacancies {P : Parts V} (ok : PackIn G univ P)
    (D : J→Finset V) (sep : (↑(univ:Finset J):Set J).PairwiseDisjoint D)
    (p q : J×Fin 3→V) (mate : J×Fin 3→J×Fin 3) (pair : Function.Involutive mate)
    (mirror : ∀ s, p (mate s)=q s)
    (seams : ∀ i, Seam (G:=G) (D i) (fun j=>p (i,j)) (fun j=>q (i,j)))
    (localResidue : ∀ i,(D i).card%3=2)
    (K : J→SimpleGraph V) (r : J→V) (outside : ∀ i,r i∉D i)
    (kept : ∀ i, ∀ x∈D i, ∀ y∈D i, G.Adj x y → (K i).Adj x y)
    (cap : ∀ i j,(K i).Adj (r i) (p (i,j)))
    (bad : ∀ i, ¬Closed (K i) (insert (r i) (D i))) :
    Fintype.card J≤2*((univ:Finset V)\P.biUnion id).card := by
  classical
  let W := P.biUnion id
  let h : J→ℕ := fun i=>(D i\W).card
  let w : J×Fin 3→ℕ := fun s=>width P (D s.1) (p s) (q s)
  have opp (s : J×Fin 3) : Opposite (w s) (w (mate s)) := by
    let t := mate s
    have one : p t=q s := mirror s
    have two : q t=p s := by rw [←mirror t,show mate t=s from pair s]
    have ne : s.1≠t.1 := by
      intro eq
      have hl : p t∈D t.1 := (seams t.1).left t.2
      have hr : q s∉D s.1 := (seams s.1).right s.2
      exact hr (eq.symm ▸ (one ▸ hl : q s∈D t.1))
    exact opposite_at_shared_seam ok (seams s.1) (seams t.1)
      (sep (mem_univ _) (mem_univ _) ne) s.2 t.2 one two
  have sig (i : J) : Signature (G:=G) (D i∩W) (fun j=>p (i,j)) (fun j=>w (i,j)) :=
    signature_of_partially_covered_cell ok (seams i)
  have residue (i : J) : ((∑ j : Fin 3,w (i,j))+h i)%3=2 := by
    have congr := width_congruence (sig i)
    have cc := card_sdiff_add_card_eq_card (show D i∩W⊆D i from inter_subset_left)
    have eq : D i\(D i∩W) = D i\W := by
      ext v
      simp only [mem_sdiff,mem_inter]
      tauto
    rw [eq,add_comm] at cc
    change (D i∩W).card + h i = (D i).card at cc
    rw [Nat.add_mod,congr,←Nat.add_mod,cc]
    exact localResidue i
  have bad2 (i : J) (no : h i=0) (exp : (∑ j : Fin 3,w (i,j))=2) : False := by
    have empty : D i\W=∅ := card_eq_zero.mp no
    have full : D i⊆W := by
      intro v vd
      by_contra nv
      have hv : v∈D i\W := mem_sdiff.mpr ⟨vd,nv⟩
      rw [empty] at hv
      exact not_mem_empty _ hv
    exact bad i (export_two_caps (signature_of_covered_cell ok full (seams i))
      exp (outside i) (kept i) (cap i))
  have count := ports_force_half_defect w mate pair opp
    (fun s=>width_le_two ok ((seams s.1).right s.2)) h residue bad2
  have tally : (∑ i,h i)≤((univ:Finset V)\W).card := by
    have dj : (↑(univ : Finset J) : Set J).PairwiseDisjoint (fun i=>D i\W) :=
      fun i hi j hj ne => (sep hi hj ne).mono sdiff_subset sdiff_subset
    have sub : univ.biUnion (fun i=>D i\W) ⊆ (univ:Finset V)\W := by
      intro v hv
      obtain ⟨i,_,ih⟩ := mem_biUnion.mp hv
      exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp ih).2⟩
    have b := card_le_card sub
    rw [card_biUnion dj] at b
    exact b
  change Fintype.card J≤2*((univ:Finset V)\W).card
  omega

#print axioms bad_caps_force_half_vacancies
end KelmansCactus.NearPerfectSharpGraph
