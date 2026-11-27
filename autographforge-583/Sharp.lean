import Row583
import Row574
import Mathlib.Tactic.Ring

namespace SlaterEdges583
open Finset SimpleGraph EulerDom574 TriangleMatching1078
variable {n : ℕ}

private abbrev Partner (x : Core n) := {i : Key n // i ≠ x.1} × Bool

private theorem partner_card (x : Core n) : Fintype.card (Partner x) = (n+1)*2 := by
  rw [Fintype.card_prod,Fintype.card_subtype_compl (fun i => i=x.1),Fintype.card_subtype_eq]
  simp [Key]

/-- Count an ordered pair from different groups by first choosing its first core. -/
private def crossEquiv (n : ℕ) : Cross n ≃ (Σ x : Core n, Partner x) where
  toFun p := ⟨p.val.1,⟨p.val.2.1,p.property.symm⟩,p.val.2.2⟩
  invFun p := ⟨(p.1,(p.2.1.val,p.2.2)),p.2.1.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def capacity (n : ℕ) := 3 + 8*(n+1)*(n+2)

private theorem family_order (n : ℕ) : Fintype.card (Vtx n) = (n+2)*capacity n := by
  have count := Fintype.card_congr (crossEquiv n)
  rw [Fintype.card_sigma] at count
  simp only [partner_card,sum_const,card_univ,smul_eq_mul] at count
  change Fintype.card (Core n ⊕ (Key n ⊕ (Cross n × Fin (2*(n+2))))) = _
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Core,Key] at count ⊢
  rw [count]
  unfold capacity
  ring

/-- List all possible neighbors of a core x. The first two choices give its
mate and its parity connector. The Boolean in the last choice selects the
order of the distinguished pair of cores. -/
private abbrev Slots (x : Core n) := Unit ⊕ (Unit ⊕ (Bool × Partner x × Fin (2*(n+2))))

private def candidate (x : Core n) : Slots x → Vtx n
  | .inl _ => .inl (mate x)
  | .inr (.inl _) => .inr (.inl (if x.2 then x.1-1 else x.1))
  | .inr (.inr (false,(j,b),t)) => .inr (.inr (⟨(x,(j.val,b)),j.property.symm⟩,t))
  | .inr (.inr (true,(j,b),t))  => .inr (.inr (⟨((j.val,b),x),j.property⟩,t))

private theorem lists_neighbors (x : Core n) {y : Vtx n} (h : (graph n).Adj (.inl x) y) :
    ∃ a : Slots x, candidate x a = y := by
  rcases y with c|i|⟨⟨⟨a,b⟩,different⟩,t⟩
  · change c = mate x at h
    exact ⟨.inl (),congrArg Sum.inl h.symm⟩
  · refine ⟨.inr (.inl ()),?_⟩
    change x=(i,false) ∨ x=(i+1,true) at h
    rcases h with rfl|rfl <;> simp [candidate]
  · change x=a ∨ x=b at h
    rcases h with rfl|rfl
    · exact ⟨.inr (.inr (false,(⟨b.1,different.symm⟩,b.2),t)),rfl⟩
    · exact ⟨.inr (.inr (true,(⟨a.1,different⟩,a.2),t)),rfl⟩

private theorem degree_bound (v : Vtx n) : (graph n).degree v ≤ capacity n - 1 := by
  classical
  rcases v with x|o
  · have sub : (graph n).neighborFinset (.inl x) ⊆ univ.image (candidate x) := by
      intro y hy
      obtain ⟨a,ha⟩ := lists_neighbors x (((graph n).mem_neighborFinset _ _).mp hy)
      exact mem_image.mpr ⟨a,mem_univ _,ha⟩
    have h := (card_le_card sub).trans card_image_le
    rw [card_neighborFinset_eq_degree,card_univ] at h
    have count : Fintype.card (Slots x) + 1 = capacity n := by
      simp only [Slots,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_unit,
        Fintype.card_fin,partner_card]
      rw [Fintype.card_subtype_compl (fun i => i=x.1),Fintype.card_subtype_eq]
      simp only [Key,Fintype.card_fin,Nat.add_sub_cancel]
      rw [show n+2-1 = n+1 by omega]
      unfold capacity
      ring
    omega
  · rw [outside_degree]
    unfold capacity
    omega

/-- Maximum closed-neighborhood capacity bounds the entire feasible prefix.
This is the row 1915 maximum-degree argument in the notation of row 583. -/
theorem slater_mass {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (deg : ∀ v, G.degree v ≤ d) : Fintype.card V ≤ (d+1)*slater G := by
  have prefixBound (l : List ℕ) (k : ℕ) (bound : ∀ t ∈ l, t ≤ d) :
      (l.take k).sum ≤ k*d := by
    induction l generalizing k with
    | nil => simp
    | cons a l ih =>
      cases k with
      | zero => simp
      | succ k =>
        have h := bound a (by simp)
        have tail := ih k (fun t ht => bound t (List.mem_cons_of_mem a ht))
        simp only [List.take_succ_cons,List.sum_cons,Nat.succ_mul]
        omega
  have bounded (t : ℕ) (h : t ∈ degreesDesc G) : t ≤ d := by
    obtain ⟨v,_,rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort (· ≥ ·)).mp h)
    exact deg v
  have attained : Fintype.card V ≤ slater G + ((degreesDesc G).take (slater G)).sum :=
    Nat.sInf_mem (s := {k | Fintype.card V ≤ k + ((degreesDesc G).take k).sum})
      ⟨Fintype.card V,Nat.le_add_right _ _⟩
  have h := prefixBound (degreesDesc G) (slater G) bounded
  rw [Nat.succ_mul,Nat.mul_comm d]
  omega

/-- For every k = n+2, the inequality is sharp on a connected Eulerian K4-free
graph even though the vertex domination number exceeds the Slater number by k−1. -/
theorem sharp (n : ℕ) : 2 ≤ Fintype.card (Vtx n) ∧ (graph n).CliqueFree 4 ∧
    (graph n).Connected ∧ (∀ v, Even ((graph n).degree v)) ∧
    slater (graph n) = n+2 ∧ lineDomination (graph n) = n+2 ∧
    AutoGraphForge378.minMaximalMatching (graph n) = n+2 ∧ domination (graph n) = 2*(n+2)-1 := by
  obtain ⟨order,conn,even,tri,dom,edge,matching⟩ := family n
  have noThree : (graph n).CliqueFree 3 := by
    intro s h
    obtain ⟨a,b,c,ab,ac,bc,_⟩ := is3Clique_iff.mp h
    exact tri a b c ab bc ac.symm
  have upperBound := eulerian (graph n) order conn even
  have lower := slater_mass (graph n) _ degree_bound
  have positive : 0 < capacity n := by simp [capacity]
  rw [Nat.sub_add_cancel positive,family_order,Nat.mul_comm (n+2)] at lower
  have size := Nat.le_of_mul_le_mul_left lower positive
  exact ⟨order,noThree.mono (by decide),conn,even,by omega,edge,matching,dom⟩

#print axioms sharp
end SlaterEdges583
