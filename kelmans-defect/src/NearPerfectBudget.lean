import ThreePort

open Finset
namespace KelmansCactus.NearPerfectBudget
variable {I : Type*} [DecidableEq I] [Fintype I]

private theorem bound_three {w : Fin 3 → ℕ} (bounded : ∀ j,w j≤2)
    (residue : (∑ j : Fin 3,w j)%3=2) (bad : (∑ j : Fin 3,w j)≠2) :
    ∃ i j, i≠j ∧ w i=2 ∧ w j=2 := by
  have univ3 : (univ:Finset (Fin 3))={0,1,2} := by decide
  have eq : (∑ j : Fin 3,w j)=w 0+w 1+w 2 := by
    rw [univ3,sum_insert (by decide : (0:Fin 3)∉({1,2}:Finset (Fin 3))),
      sum_insert (by decide : (1:Fin 3)∉({2}:Finset (Fin 3))),sum_singleton]
    omega
  rw [eq] at residue bad
  have b0 := bounded 0
  have b1 := bounded 1
  have b2 := bounded 2
  by_cases a : w 0=2
  · by_cases b : w 1=2
    · exact ⟨0,1,by decide,a,b⟩
    · exact ⟨0,2,by decide,a,by omega⟩
  · exact ⟨1,2,by decide,by omega,by omega⟩

private theorem count_eq_indicator {A : Type*} (s : Finset A) (p : A→Prop) [DecidablePred p] :
    (s.filter p).card = ∑ v∈s, if p v then (1:ℕ) else 0 := by
  rw [←sum_filter]
  simp

/-- Endpoint accounting for an amplified packing. Matching seams
can have width two at at most one end. A fully covered bad
0-cap cell needs two wide ends by the local residue and the
impossibility of total export two. Thus at least one quarter
of the cells must contain a hole. -/
theorem ports_force_quarter_defect (w : I × Fin 3 → ℕ) (mate : I × Fin 3 → I × Fin 3)
    (pair : Function.Involutive mate) (bounded : ∀ p,w p≤2)
    (atMostOneWide : ∀ p, w p=2 → w (mate p)≠2)
    (good : Finset I) (residue : ∀ i∈good,(∑ j : Fin 3,w (i,j))%3=2)
    (badTwo : ∀ i∈good,(∑ j : Fin 3,w (i,j))≠2)
    (h : ℕ) (covers : Fintype.card I-good.card≤h) :
    Fintype.card I≤4*h := by
  classical
  let W : Finset (I × Fin 3) := univ.filter (fun p => w p=2)
  have WI : Disjoint W (W.image mate) := by
    apply disjoint_left.mpr
    intro p wp mp
    obtain ⟨q,wq,rfl⟩ := mem_image.mp mp
    exact atMostOneWide q (mem_filter.mp wq).2 (mem_filter.mp wp).2
  have upper : 2*W.card≤3*Fintype.card I := by
    have b := card_le_card (subset_univ (W∪W.image mate))
    rw [card_union_of_disjoint WI,card_image_of_injective _ pair.injective,card_univ,
      Fintype.card_prod] at b
    simp at b
    omega
  have widthCard (i : I) (gi : i∈good) :
      2≤((univ : Finset (Fin 3)).filter (fun j => w (i,j)=2)).card := by
    obtain ⟨p,q,pq,wp,wq⟩ := bound_three (fun j => bounded (i,j))
      (residue i gi) (badTwo i gi)
    have sub : ({p,q}:Finset (Fin 3))⊆univ.filter (fun j => w (i,j)=2) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact mem_filter.mpr ⟨mem_univ _,wp⟩
      · exact mem_filter.mpr ⟨mem_univ _,wq⟩
    have k := card_le_card sub
    simpa [pq] using k
  have total : W.card = ∑ i : I, ((univ : Finset (Fin 3)).filter (fun j => w (i,j)=2)).card := by
    change (univ.filter (fun p => w p=2)).card=_
    rw [count_eq_indicator]
    simp only [count_eq_indicator]
    exact Fintype.sum_prod_type _
  have lo : 2*good.card≤W.card := by
    calc
      2*good.card = ∑ _∈good, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i∈good, ((univ : Finset (Fin 3)).filter (fun j => w (i,j)=2)).card := sum_le_sum widthCard
      _ ≤ _ := by
        rw [total]
        exact sum_le_sum_of_subset (subset_univ good)
  have g := card_le_card (subset_univ good)
  rw [card_univ] at g
  omega

#print axioms ports_force_quarter_defect
end KelmansCactus.NearPerfectBudget
