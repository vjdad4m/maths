import MinimalSeams

open Finset
namespace KelmansCactus.AtomicBridge
open ThreePort Substitute MinimalSeams

variable {V : Type*} [DecidableEq V] {G K : SimpleGraph V}

/-- A factor of an order-four cap after deleting one of its ports
yields a residue-zero open signature with width one at that same port.
Deleting the cap root leaves either one two-vertex fragment at a different
port or singleton fragments at both other ports. -/
theorem zero_signature_at_port {A : Finset V} {r : V} {p : Fin 3→V} (i : Fin 3)
    (pin : p i∈A) (root : r∉A)
    (fac : Closed K (insert r (A.erase (p i))))
    (nbr : ∀ x∈A,K.Adj r x→∃ j,p j=x)
    (keep : ∀ x∈A,∀ y∈A,K.Adj x y→G.Adj x y) :
    ∃ w,Signature (G:=G) A p w ∧ w i=1 ∧
      ((∃ j, j≠i ∧ ∀ k,w k=(if k=i then 1 else if k=j then 2 else 0)) ∨
        ∀ k,w k=1) := by
  let B := A.erase (p i)
  have sub : B⊆A := erase_subset _ _
  obtain ⟨w,⟨F,hF,d,P,hP⟩,rec⟩ := cap_supplies_recoverable (G:=G) (A:=B) (p:=p)
    fac (fun h=>root (sub h)) (fun x hx=>nbr x (sub hx))
      (fun x hx y hy=>keep x (sub hx) y (sub hy))
  have avoid (j : Fin 3) (h : p j=p i) : F j=∅ := by
    refine not_nonempty_iff_eq_empty.mp ?_
    intro ne
    have contra := (hF j).2.inside ((hF j).2.includes ne)
    exact (mem_erase.mp contra).1 h
  have no_i : F i=∅ := avoid i rfl
  have z : w i=0 := by rw [←(hF i).1,no_i,card_empty]
  let D (j : Fin 3) := if j=i then ({p i} : Finset V) else F j
  let W (j : Fin 3) := if j=i then 1 else w j
  refine ⟨W,⟨D,?_,?_,P,?_⟩,by simp [W],?_⟩
  · intro j
    by_cases e : j=i
    · subst j
      simp only [D,W,if_pos rfl,card_singleton,true_and]
      exact ⟨singleton_subset_iff.mpr pin,by simp,by simp⟩
    · simp only [D,W,if_neg e]
      exact ⟨(hF j).1,⟨fun x hx=>sub ((hF j).2.inside hx),
        (hF j).2.includes,(hF j).2.star⟩⟩
  · intro j k ne
    by_cases a : j=i
    · subst j
      have b : k≠i := ne.symm
      simp only [D,if_pos rfl,if_neg b]
      exact disjoint_left.mpr fun x hx hy=>
        (mem_erase.mp ((hF k).2.inside hy)).1 (mem_singleton.mp hx)
    · by_cases b : k=i
      · subst k
        simp only [D,if_neg a,if_pos rfl]
        exact disjoint_left.mpr fun x hx hy=>
          (mem_erase.mp ((hF j).2.inside hx)).1 (mem_singleton.mp hy)
      · simpa [D,a,b] using d j k ne
  · have eq : A \ univ.biUnion D=B \ univ.biUnion F := by
      ext x
      simp only [mem_sdiff,mem_biUnion,mem_univ,true_and,not_exists,B,mem_erase]
      change x∈A ∧ (∀ j,x∉D j) ↔ (x≠p i ∧ x∈A) ∧ (∀j,x∉F j)
      constructor
      · rintro ⟨xa,ds⟩
        have xn : x≠p i := by simpa [D] using ds i
        refine ⟨⟨xn,xa⟩,?_⟩
        intro j
        by_cases e : j=i
        · subst j
          simp [no_i]
        · simpa [D,e] using ds j
      · rintro ⟨⟨xn,xa⟩,fs⟩
        refine ⟨xa,?_⟩
        intro j
        by_cases e : j=i
        · subst j
          simpa [D] using xn
        · simpa [D,e] using fs j
    rw [eq]
    exact hP
  · rcases rec with ⟨j,eq⟩|⟨j,k,jk,eq⟩
    · have ji : j≠i := by
        intro h
        subst j
        simp [eq] at z
      exact Or.inl ⟨j,ji,fun k=>by simp [W,eq]⟩
    · have ij : i≠j := by
        intro h
        subst j
        simp [eq] at z
      have ik : i≠k := by
        intro h
        subst k
        simp [eq] at z
      right
      intro l
      have full : ∀ (a b c d : Fin 3), a≠b→a≠c→b≠c→d=a ∨ d=b ∨ d=c := by decide
      have exhaustive := full i j k l ij ik jk
      rcases exhaustive with h|h|h
      · simp [W,h]
      · simp [W,eq,h,ij.symm]
      · simp [W,eq,h,ik.symm]

#print axioms zero_signature_at_port
end KelmansCactus.AtomicBridge
