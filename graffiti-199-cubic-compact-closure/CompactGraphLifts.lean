import CompactOmission
import CompactExtensionBase

open private three_names_exhaust_neighbors from DepletedFootprint
open private traceable_of_omission_permutation from OmissionSplice

namespace Graffiti199Depleted.CompactOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}

def middle (f : Fin 8 ↪ V) : List V := [f 0,f 1,f 2,f 3,f 4,f 5,f 6]

private theorem middle_cases (f : Fin 8 ↪ V) (i : Fin 8) :
    f i ∈ middle f ∨ i = 7 := by fin_cases i <;> simp [middle]

theorem core_perm (f : Fin 8 ↪ V) {P : List (Fin 8)} (h : P.Perm (List.finRange 8)) :
    (P.map f).Perm (f 7 :: middle f) := by
  have eq : (List.finRange 8).map (f : Fin 8 → V) = middle f ++ [f 7] := by
    have : List.finRange 8 = ([0,1,2,3,4,5,6,7] : List (Fin 8)) := by decide
    rw [this]
    rfl
  exact (eq ▸ h.map f).trans List.perm_middle

private def extendedFun {n : ℕ} (f : Fin 8 ↪ V) (x : Fin n ↪ V) : Fin (8+n) → V :=
  Fin.addCases f x

private theorem extendedFun_left {n : ℕ} (f : Fin 8 ↪ V) (x : Fin n ↪ V) (i : Fin 8) :
    extendedFun f x (Fin.castAdd n i) = f i := by
  unfold extendedFun
  exact Fin.addCases_left i

private theorem extendedFun_right {n : ℕ} (f : Fin 8 ↪ V) (x : Fin n ↪ V) (j : Fin n) :
    extendedFun f x (Fin.natAdd 8 j) = x j := by
  unfold extendedFun
  exact Fin.addCases_right j

/-- The outside labels can be appended to the eight core labels. -/
def extend {n : ℕ} (f : Fin 8 ↪ V) (x : Fin n ↪ V)
    (off : ∀ i j, x j ≠ f i) : Fin (8+n) ↪ V where
  toFun := extendedFun f x
  inj' := by
    intro i
    refine Fin.addCases (m := 8) (n := n) (motive := fun i => ∀ j,
      extendedFun f x i = extendedFun f x j → i = j) ?_ ?_ i
    · intro a u
      refine Fin.addCases (m := 8) (n := n) ?_ ?_ u
      · intro b h
        have eq : f a = f b := by simpa only [extendedFun_left] using h
        rw [f.injective eq]
      · intro b h
        exact (off a b (by simpa only [extendedFun_left,extendedFun_right] using h.symm)).elim
    · intro a u
      refine Fin.addCases (m := 8) (n := n) ?_ ?_ u
      · intro b h
        exact (off b a (by simpa only [extendedFun_left,extendedFun_right] using h)).elim
      · intro b h
        have eq : x a = x b := by simpa only [extendedFun_right] using h
        rw [x.injective eq]

@[simp] theorem extend_left {n : ℕ} (f : Fin 8 ↪ V) (x : Fin n ↪ V) (off) (i : Fin 8) :
    extend f x off (Fin.castAdd n i) = f i := extendedFun_left f x i

@[simp] theorem extend_right {n : ℕ} (f : Fin 8 ↪ V) (x : Fin n ↪ V) (off) (j : Fin n) :
    extend f x off (Fin.natAdd 8 j) = x j := extendedFun_right f x j

def ProfileAt (G : SimpleGraph V) (f : Fin 8 ↪ V) (v : V) (m : Profile) : Prop :=
  ∀ i, G.Adj v (f i) ↔ contact m i = true

theorem extension_chart {n : ℕ} {f : Fin 8 ↪ V} {x : Fin n ↪ V} {off}
    {k : Fin 6} {m : Fin n → Profile} {b : Fin n → Fin n → Bool}
    (core : ∀ i j, G.Adj (f i) (f j) ↔ adjacent (coreRows k) i j = true)
    (profiles : ∀ j, ProfileAt G f (x j) (m j))
    (links : ∀ u v, G.Adj (x u) (x v) ↔ b u v = true) :
    ∀ i j, G.Adj (extend f x off i) (extend f x off j) ↔ extension k m b i j = true := by
  apply Fin.addCases
  · intro i
    apply Fin.addCases
    · intro j
      simpa only [extend_left,extension,Fin.addCases_left] using core i j
    · intro j
      simpa only [extend_left,extend_right,extension,Fin.addCases_left,Fin.addCases_right,G.adj_comm]
        using profiles j i
  · intro i
    apply Fin.addCases
    · intro j
      simpa only [extend_left,extend_right,extension,Fin.addCases_left,Fin.addCases_right]
        using profiles i j
    · intro j
      simpa only [extend_right,extension,Fin.addCases_right] using links i j

theorem six_tree_absurd [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} {g : Fin n ↪ V} {edge : Fin n → Fin n → Bool} {T : Fin 6 → Fin n}
    (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (g i) (g j) ↔ edge i j = true)
    (tree : SixTree edge T) : False := by
  let order : Fin 6 ↪ V := ⟨g ∘ T,fun i j h => tree.1 i j (g.injective h)⟩
  have six := Catalogue.six_le_treeNumber_of_ordering (G := G) order (by
    intro i i0
    obtain ⟨j,e,lt,unique⟩ := tree.2 i i0
    exact ⟨j,(chart _ _).mpr e,lt,fun h eh lh => unique h ((chart _ _).mp eh) lh⟩)
  omega

theorem chain_from_chart {n : ℕ} {g : Fin n ↪ V} {e : Fin n → Fin n → Bool}
    (chart : ∀ i j, G.Adj (g i) (g j) ↔ e i j = true) {P : List (Fin n)}
    (route : P.Chain' (fun i j => e i j = true)) : (P.map g).Chain' G.Adj :=
  List.chain'_map_of_chain' g (fun i j e => (chart i j).mpr e) route

variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem code_profile (f : Fin 8 ↪ V) (v : V) (offZ : ¬ G.Adj v (f 7)) :
    ∃ m, ProfileAt G f v m := by
  let r : Row := ⟨decide (G.Adj v (f 0)),decide (G.Adj v (f 1)),decide (G.Adj v (f 2)),
    decide (G.Adj v (f 3)),decide (G.Adj v (f 4)),decide (G.Adj v (f 5)),
    decide (G.Adj v (f 6))⟩
  refine ⟨code r,?_⟩
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp [contact_omission,offZ]
  · intro j
    rw [contact_code]
    fin_cases j <;> simp [flags,r]

omit [DecidableEq V] in
theorem cubic_on_core (f : Fin 8 ↪ V) {k : Fin 6}
    (core : ∀ i j, G.Adj (f i) (f j) ↔ adjacent (coreRows k) i j = true)
    (d : G.degree (f 1) = 3 ∨ G.degree (f 3) = 3 ∨ G.degree (f 5) = 3) :
    G.degree (f (mate k)) = 3 := by
  classical
  have off {u a b c i : Fin 8} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
      (du : G.degree (f u) = 3)
      (e₁ : adjacent (coreRows k) u a = true) (e₂ : adjacent (coreRows k) u b = true)
      (e₃ : adjacent (coreRows k) u c = true) (hi : i ∉ [a,b,c]) :
      adjacent (coreRows k) u i = false := by
    apply Bool.eq_false_iff.mpr
    intro e
    obtain ⟨j,hj,eq⟩ := three_names_exhaust_neighbors f ab ac bc du
      ((core _ _).mpr e₁) ((core _ _).mpr e₂) ((core _ _).mpr e₃) _ ((core _ _).mpr e)
    exact hi (f.injective eq ▸ hj)
  rcases d with d|d|d
  · have o (i : Fin 8) (hi : i ∉ ([0,2,7] : List (Fin 8))) :
        adjacent (coreRows k) 1 i = false :=
      off (by decide) (by decide) (by decide) d rfl rfl rfl hi
    rw [(mate_of_slot k).1 ⟨o 4 (by decide),o 6 (by decide)⟩]
    exact d
  · have o (i : Fin 8) (hi : i ∉ ([2,4,7] : List (Fin 8))) :
        adjacent (coreRows k) 3 i = false :=
      off (by decide) (by decide) (by decide) d rfl rfl rfl hi
    rw [(mate_of_slot k).2.1 ⟨o 0 (by decide),o 6 (by decide)⟩]
    exact d
  · have o (i : Fin 8) (hi : i ∉ ([4,6,7] : List (Fin 8))) :
        adjacent (coreRows k) 5 i = false :=
      off (by decide) (by decide) (by decide) d rfl rfl rfl hi
    rw [(mate_of_slot k).2.2 ⟨o 0 (by decide),o 2 (by decide)⟩]
    exact d

omit [DecidableEq V] in
/-- A cubic core vertex with three neighbors in the core has no external contacts. -/
private theorem no_external_at_cubic (f : Fin 8 ↪ V) {v : V}
    (off : ∀ i, v ≠ f i) {u a b c : Fin 8} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (degree : G.degree (f u) = 3)
    (e₁ : G.Adj (f u) (f a)) (e₂ : G.Adj (f u) (f b)) (e₃ : G.Adj (f u) (f c)) :
    ¬ G.Adj v (f u) := by
  intro adj
  obtain ⟨i,_,eq⟩ := three_names_exhaust_neighbors f ab ac bc degree e₁ e₂ e₃ v adj.symm
  exact off i eq.symm

omit [DecidableRel G.Adj] [Fintype V] in
theorem trace_of_middle_replacement (p : PathOn G {v | v ≠ z})
    {U M N R : List V} (old : p.vertices = U ++ M ++ R)
    (mne : M ≠ []) (nne : N ≠ []) (hp : N.head? = M.head?) (tp : N.getLast? = M.getLast?)
    (perm : N.Perm (z :: M)) (chain : N.Chain' G.Adj) : Catalogue.Traceable G := by
  have ch : (U ++ M ++ R).Chain' G.Adj := old ▸ p.chain
  have left : (U ++ N).Chain' G.Adj := ch.left_of_append.left_of_append.append chain (by
    intro u hu v hv
    rw [hp] at hv
    exact (List.chain'_append.mp ch.left_of_append).2.2 u hu v hv)
  have all : (U ++ N ++ R).Chain' G.Adj := left.append ch.right_of_append (by
    intro u hu v hv
    rw [List.getLast?_append_of_ne_nil U nne,tp,← List.getLast?_append_of_ne_nil U mne] at hu
    exact (List.chain'_append.mp ch).2.2 u hu v hv)
  have transport : (U ++ N ++ R).Perm (z :: p.vertices) := by
    rw [old]
    exact ((perm.append_left U).append_right R).trans (by
      simpa only [List.append_assoc,List.cons_append] using
        (List.perm_middle (a := z) (l₁ := U) (l₂ := M ++ R)))
  exact traceable_of_omission_permutation p transport all

#print axioms trace_of_middle_replacement

end Graffiti199Depleted.CompactOmission
