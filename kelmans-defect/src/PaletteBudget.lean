import ThreePort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

open Finset
namespace KelmansCactus.PaletteBudget
open ThreePort

def switch (a : Fin 3) : Fin 3 := if a=1 then 2 else if a=2 then 1 else 0
private theorem twice : ∀ a : Fin 3, switch (switch a) = a := by decide

def dual {I : Type*} : (I → Fin 3) ↪ (I → Fin 3) where
  toFun w i := switch (w i)
  inj' := by
    intro w z e
    funext i
    have c := congrFun e i
    change switch (w i) = switch (z i) at c
    simpa only [twice] using congrArg switch c

private theorem coord : ∀ a : Fin 3, Opposite a.val (switch a).val := by
  unfold Opposite
  decide

def pool (d : ℕ) (r : Fin 3) : Finset (Fin d → Fin 3) :=
  univ.filter fun w => (∑ i, (w i).val)%3 = r.val

private theorem sum_split {d : ℕ} (w : Fin (d+1) → ℕ) :
    (∑ i, w i) = (∑ i : Fin d, w i.castSucc) + w (Fin.last d) := by
  have h : (univ : Finset (Fin (d+1))) = insert (Fin.last d) (univ.map Fin.castSuccEmb) := by
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp
    · exact iff_true_intro (mem_univ _) |>.trans
        (iff_true_intro (mem_insert_of_mem (mem_map.mpr ⟨k,mem_univ _,rfl⟩))).symm
  have hn : Fin.last d ∉ (univ : Finset (Fin d)).map Fin.castSuccEmb := by
    intro he
    obtain ⟨j,_,hj⟩ := mem_map.mp he
    have h : j.val=d := congrArg Fin.val hj
    omega
  calc
    (∑ i : Fin (d+1), w i) = ∑ i ∈ insert (Fin.last d) (univ.map Fin.castSuccEmb), w i :=
      Finset.sum_congr h (fun _ _ => rfl)
    _ = _ := by
      rw [sum_insert hn,sum_map,add_comm]
      simp only [Fin.castSuccEmb_apply]

private def digit {d : ℕ} (r : Fin 3) (x : Fin d → Fin 3) : Fin 3 :=
  ⟨(r.val+3-(∑ i, (x i).val)%3)%3,Nat.mod_lt _ (by decide)⟩

private def fill {d : ℕ} (r : Fin 3) : (Fin d → Fin 3) ↪ (Fin (d+1) → Fin 3) where
  toFun x := Fin.snoc x (digit r x)
  inj' := by
    intro x y h
    funext i
    have h' := congrFun h i.castSucc
    simpa [Fin.snoc_castSucc] using h'

theorem pool_card_succ (d : ℕ) (r : Fin 3) : (pool (d+1) r).card = 3^d := by
  have h : pool (d+1) r = (univ : Finset (Fin d → Fin 3)).map (fill r) := by
    ext w
    constructor
    · intro hw
      have wh := (mem_filter.mp hw).2
      let pre : Fin d → Fin 3 := fun i => w i.castSucc
      have hsplit := sum_split (fun i => (w i).val)
      have hl := (w (Fin.last d)).isLt
      have rr := r.isLt
      have hmod : (∑ i : Fin d, (pre i).val) + (w (Fin.last d)).val =
          (∑ i : Fin (d+1), (w i).val) := hsplit.symm
      have eql : digit r pre = w (Fin.last d) := by
        apply Fin.ext
        change (r.val+3-(∑ i, (pre i).val)%3)%3 = (w (Fin.last d)).val
        omega
      refine mem_map.mpr ⟨pre,mem_univ _,?_⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [fill,Fin.snoc_last] using eql
      · simp [fill,pre,Fin.snoc_castSucc]
    · intro hw
      obtain ⟨pre,_,rfl⟩ := mem_map.mp hw
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      rw [sum_split]
      simp only [fill,Function.Embedding.coeFn_mk,Fin.snoc_castSucc,Fin.snoc_last,digit]
      have rr := r.isLt
      omega
  rw [h,card_map,card_univ,Fintype.card_pi]
  simp

theorem pool_three (r : Fin 3) : (pool 3 r).card=9 := pool_card_succ 2 r
theorem pool_four (r : Fin 3) : (pool 4 r).card=27 := pool_card_succ 3 r
theorem pool_five (r : Fin 3) : (pool 5 r).card=81 := pool_card_succ 4 r

private theorem entails {d : ℕ} {w : Fin d → Fin 3} :
    (∑ i, (w i).val) + (∑ i, ((dual w) i).val) = ∑ i : Fin d, (if w i = 0 then 0 else 3) := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have ts : ∀ a : Fin 3, a.val + (switch a).val = if a=0 then 0 else 3 := by decide
  exact ts (w i)

private theorem dual_sum {d : ℕ} (w : Fin d → Fin 3) :
    3 ∣ (∑ i, (w i).val) + (∑ i, ((dual w) i).val) := by
  rw [entails]
  apply Finset.dvd_sum
  intro i _
  by_cases h : w i=0 <;> simp [h]

theorem overlap {X : Type*} [DecidableEq X] {A B U : Finset X}
    (ha : A ⊆ U) (hb : B ⊆ U) (wide : U.card < A.card+B.card) :
    ∃ x ∈ A, x ∈ B := by
  by_contra! dis
  have hd := disjoint_left.mpr dis
  have hh := card_le_card (union_subset ha hb)
  rw [card_union_of_disjoint hd] at hh
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Matching-seam pigeonhole threshold, exact for any finite number of ports.
A candidate palette consists of certified states, not an assumption
that all arithmetic states are attainable. -/
theorem large_palettes_glue {d : ℕ} {A : Finset V} {p q : Fin d → V}
    (seam : Seam (G:=G) A p q)
    (order : Fintype.card V % 3 = 0)
    (L R : Finset (Fin d → Fin 3))
    (l : ∀ s ∈ L, Signature (G:=G) A p (fun i => (s i).val))
    (r : ∀ s ∈ R, Signature (G:=G) Aᶜ q (fun i => (s i).val))
    (wide : (pool d ⟨A.card%3,Nat.mod_lt _ (by decide)⟩).card < L.card+R.card) :
    KelmansStarter.HasP3Factor G := by
  let C := pool d ⟨A.card%3,Nat.mod_lt _ (by decide)⟩
  have left : L ⊆ C := by
    intro s hs
    exact mem_filter.mpr ⟨mem_univ _, width_congruence (l s hs)⟩
  have right : R.map dual ⊆ C := by
    intro s hs
    obtain ⟨t,ht,rfl⟩ := mem_map.mp hs
    have hw := width_congruence (r t ht)
    have hD := dual_sum t
    have cc : A.card + Aᶜ.card = Fintype.card V := by
      rw [← card_union_of_disjoint (disjoint_compl_right : Disjoint A Aᶜ)]
      have cov : A ∪ Aᶜ = univ := by ext u; simp
      rw [cov,card_univ]
    have eq : (∑ i, ((dual t) i).val)%3 = A.card%3 := by omega
    exact mem_filter.mpr ⟨mem_univ _,eq⟩
  obtain ⟨s,ls,rs⟩ := overlap left right (by simpa [C] using wide)
  obtain ⟨t,tr,e⟩ := mem_map.mp rs
  have hmatch : ∀ i, Opposite (s i).val (t i).val := by
    intro i
    rw [← e]
    change Opposite (switch (t i)).val (t i).val
    exact (show ∀ u : Fin 3, Opposite (switch u).val u.val from by unfold Opposite; decide) (t i)
  exact (factor_iff_signatures seam).mpr ⟨_,_,l s ls,r t tr,hmatch⟩

theorem fourteen_each_four_cut {A : Finset V} {p q : Fin 4 → V}
    (seam : Seam (G:=G) A p q) (order : Fintype.card V % 3 = 0)
    (L R : Finset (Fin 4 → Fin 3))
    (l : ∀ s ∈ L, Signature (G:=G) A p (fun i => (s i).val))
    (r : ∀ s ∈ R, Signature (G:=G) Aᶜ q (fun i => (s i).val))
    (lh : 14 ≤ L.card) (rh : 14 ≤ R.card) :
    KelmansStarter.HasP3Factor G := by
  apply large_palettes_glue seam order L R l r
  rw [pool_four]
  omega

theorem fortyone_each_five_cut {A : Finset V} {p q : Fin 5 → V}
    (seam : Seam (G:=G) A p q) (order : Fintype.card V % 3 = 0)
    (L R : Finset (Fin 5 → Fin 3))
    (l : ∀ s ∈ L, Signature (G:=G) A p (fun i => (s i).val))
    (r : ∀ s ∈ R, Signature (G:=G) Aᶜ q (fun i => (s i).val))
    (lh : 41 ≤ L.card) (rh : 41 ≤ R.card) :
    KelmansStarter.HasP3Factor G := by
  apply large_palettes_glue seam order L R l r
  rw [pool_five]
  omega

#print axioms pool_card_succ
#print axioms fortyone_each_five_cut
#print axioms pool_three
#print axioms pool_four
#print axioms large_palettes_glue
#print axioms fourteen_each_four_cut
end KelmansCactus.PaletteBudget
