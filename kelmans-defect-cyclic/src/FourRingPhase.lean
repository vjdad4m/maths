import FourRingAmplify

open Finset
namespace KelmansCactus.FourRingPhase
open ThreePort Substitute PathSlides ContactSlides NearPerfectCells FourRingBudget FourRingCap
noncomputable section

/-- Phase is 1 minus the exported left width, modulo three. -/
def phase (l : ℕ) : ℕ := (4-(l%3))%3

/-- A zero-hole cell can go backwards by two phases only if both
halves export exactly two vertices. This is a recoverable state. -/
theorem phase_charge {l rr n m : ℕ} (lb : l≤4) (rb : rr≤4)
    (seam : (rr+n)%3=0) (res : (l+rr+m)%3=1)
    (bad : m=0 → ¬(l=2 ∧ rr=2)) :
    1+phase l≤m+phase n := by
  unfold phase
  omega

private theorem paired_residue {a b c d : ℕ}
    (x : Opposite a c) (y : Opposite b d) : (a+b+(c+d))%3=0 := by
  rcases x with ⟨_,_⟩|⟨_,_,_,_,_⟩ <;>
    rcases y with ⟨_,_⟩|⟨_,_,_,_,_⟩ <;> omega

theorem phased_ring_budget {J : Type*} [Fintype J]
    (next : Equiv.Perm J) (w : J→Slot→ℕ) (h : J→ℕ)
    (bounds : ∀ i s,w i s≤2)
    (seams : ∀ i bit,Opposite (w i (true,bit)) (w (next i) (false,bit)))
    (res : ∀ i,(left (w i)+right (w i)+h i)%3=1)
    (bad : ∀ i,h i=0 → ¬(left (w i)=2 ∧ right (w i)=2)) :
    Fintype.card J≤∑ i,h i := by
  classical
  have l (i : J) : left (w i)≤4 := by
    have a := bounds i (false,false)
    have b := bounds i (false,true)
    unfold left
    omega
  have rr (i : J) : right (w i)≤4 := by
    have a := bounds i (true,false)
    have b := bounds i (true,true)
    unfold right
    omega
  have one (i : J) : 1+phase (left (w i))≤h i+phase (left (w (next i))) :=
    phase_charge (l i) (rr i)
      (paired_residue (seams i false) (seams i true)) (res i) (bad i)
  have tally :
      (∑ i : J,(1+phase (left (w i)))) ≤ (∑ i : J,(h i+phase (left (w (next i))))) :=
    sum_le_sum (fun i _=>one i)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Nat.mul_one] at tally
  have cancelPhase :
      (∑ i : J,phase (left (w (next i)))) = ∑ i : J,phase (left (w i)) :=
    Equiv.sum_comp next (fun i=>phase (left (w i)))
  rw [cancelPhase] at tally
  change Fintype.card J+(∑ i : J,phase (left (w i)))≤_ at tally
  omega

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V}

omit [DecidableEq J] in
/-- The phase argument on genuine graph packings. Every graph
with disjoint four-port cells linked in pairs in cyclic order,
all with unfactorable two-root caps, needs at least one vacancy
per cell, no matter which packing is chosen. -/
theorem one_vacancy_per_bad_cell {P : Parts V} (ok : PackIn G univ P)
    (D : J→Finset V) (sep : (↑(univ:Finset J):Set J).PairwiseDisjoint D)
    (p q : J→Slot→V) (next : Equiv.Perm J)
    (agree : ∀ i b,p (next i) (false,b)=q i (true,b) ∧ q (next i) (false,b)=p i (true,b))
    (seams : ∀ i,Seam (G:=G) (D i) (p i) (q i))
    (res : ∀ i,(D i).card%3=1)
    (K : J→SimpleGraph V) (r : J→Bool→V)
    (cap : ∀ i,Cap (G:=G) (K i) (D i) (p i) (r i))
    (bad : ∀ i,¬Closed (K i) (insert (r i false) (insert (r i true) (D i)))) :
    Fintype.card J ≤ ((univ:Finset V)\P.biUnion id).card := by
  classical
  let W := P.biUnion id
  let h : J→ℕ := fun i=>(D i\W).card
  let w : J→Slot→ℕ := fun i s=>width P (D i) (p i s) (q i s)
  have mate (i : J) (b : Bool) : Opposite (w i (true,b)) (w (next i) (false,b)) := by
    have ne : i≠next i := by
      intro eq
      have pin : p (next i) (false,b)∈D (next i) := (seams (next i)).left _
      have qq : q i (true,b)∈D (next i) := (agree i b).1 ▸ pin
      exact (seams i).right _ (eq.symm ▸ qq)
    exact opposite_at_shared_seam ok (seams i) (seams (next i))
      (sep (mem_univ _) (mem_univ _) ne) (true,b) (false,b) (agree i b).1 (agree i b).2
  have widths (i : J) (s : Slot) : w i s≤2 := width_le_two ok ((seams i).right s)
  have local_res (i : J) : (left (w i)+right (w i)+h i)%3=1 := by
    have part : Signature (G:=G) (D i∩W) (p i) (w i) :=
      signature_of_partially_covered_cell ok (seams i)
    have mod := width_congruence part
    rw [profile_sum] at mod
    have cc := card_sdiff_add_card_eq_card (show D i∩W⊆D i from inter_subset_left)
    have eq : D i\(D i∩W) = D i\W := by
      ext v
      simp only [mem_sdiff,mem_inter]
      tauto
    rw [eq,add_comm] at cc
    change (D i∩W).card+h i=(D i).card at cc
    rw [Nat.add_mod,mod,←Nat.add_mod,cc]
    exact res i
  have nonbalanced (i : J) (no : h i=0) (balanced : left (w i)=2 ∧ right (w i)=2) :
      False := by
    have empty : D i\W=∅ := card_eq_zero.mp no
    have full : D i⊆W := by
      intro v vd
      by_contra nv
      have hv : v∈D i\W := mem_sdiff.mpr ⟨vd,nv⟩
      rw [empty] at hv
      exact not_mem_empty _ hv
    exact bad i (export_balanced_caps (cap i)
      (signature_of_covered_cell ok full (seams i)) balanced.1 balanced.2)
  apply (phased_ring_budget next w h widths mate local_res nonbalanced).trans
  have dj : (↑(univ : Finset J) : Set J).PairwiseDisjoint (fun i=>D i\W) :=
    fun i hi j hj ne=>(sep hi hj ne).mono sdiff_subset sdiff_subset
  have sub : univ.biUnion (fun i=>D i\W)⊆(univ:Finset V)\W := by
    intro v hv
    obtain ⟨i,_,vi⟩ := mem_biUnion.mp hv
    exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp vi).2⟩
  have low := card_le_card sub
  rw [card_biUnion dj] at low
  exact low

#print axioms phase_charge
#print axioms phased_ring_budget
#print axioms one_vacancy_per_bad_cell
end
end KelmansCactus.FourRingPhase
