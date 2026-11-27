import BurnBridge
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace CycleBatch
open SimpleGraph Finset PathCycleSharpness
abbrev V := Fin 43
abbrev C := cycleGraph 43
theorem connected : C.Connected := cycleGraph_connected (n := 42)
theorem deg (v : V) : C.degree v = 2 := cycleGraph_degree_three_le
theorem eulerian : Eulerian C := ⟨connected, fun v => by rw [deg]⟩
theorem subcubic : Subcubic C := fun v => (deg v).le.trans (by decide)
theorem regular : C.IsRegularOfDegree 2 := deg

def TriangleFree {U : Type*} (G : SimpleGraph U) := ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a

theorem nbr {v w : V} (e : C.Adj v w) : w = v-1 ∨ w = v+1 := by
  have h := (C.mem_neighborFinset v w).mpr e
  simpa [cycleGraph_neighborFinset] using h

theorem triangle : TriangleFree C := by
  intro a b c ab bc ca
  have sides : ∀ i : V, ¬ C.Adj (i-1) (i+1) := by decide
  rcases nbr ab with rfl|rfl <;> rcases nbr ca.symm with rfl|rfl
  · exact bc.ne rfl
  · exact sides a bc
  · exact sides a bc.symm
  · exact bc.ne rfl

theorem k4free : C.CliqueFree 4 := by
  by_contra no
  obtain ⟨f⟩ := (not_cliqueFree_iff 4).mp no
  have edge {x y : Fin 4} (h : x ≠ y) : C.Adj (f x) (f y) :=
    f.map_adj_iff.mpr ((top_adj x y).mpr h)
  exact triangle (f 0) (f 1) (f 2) (edge (by decide)) (edge (by decide)) (edge (by decide))

theorem clawfree : ClawFree C := by
  intro v a b c va vb vc ab ac bc
  rcases nbr va with h|h <;> rcases nbr vb with h'|h' <;> rcases nbr vc with h''|h'' <;> simp_all

theorem size43 : C.edgeFinset.card = 43 := by
  have h := C.sum_degrees_eq_twice_card_edges
  simp only [deg,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at h
  omega

private def len (p : V) := min p.val (43 - p.val)
private def d (x y : V) := len (y-x)

theorem metric : (∀ x y, C.Reachable x y) ∧ ∀ x y, C.dist x y = d x y := by
  apply metric_certificate
  · intro x y
    have h : ∀ p : V, len p = 0 ↔ p=0 := by decide
    rw [d,h,sub_eq_zero,eq_comm]
  · intro x y z yz
    have step : ∀ p : V, len (p-1) ≤ len p+1 ∧ len (p+1) ≤ len p+1 := by decide
    rcases nbr yz with rfl|rfl
    · simpa only [d,sub_right_comm] using (step (y-x)).1
    · simpa only [d,add_sub_right_comm] using (step (y-x)).2
  · intro x y xy
    have reduce : ∀ p : V, p≠0 → len (p-1)+1 = len p ∨ len (p+1)+1 = len p := by decide
    have h := reduce (y-x) (sub_ne_zero.mpr xy.symm)
    have edges : ∀ p : V, C.Adj (p-1) p ∧ C.Adj (p+1) p := by decide
    rcases h with h|h
    · exact ⟨y-1,(edges y).1,by simpa only [d,sub_right_comm] using h⟩
    · exact ⟨y+1,(edges y).2,by simpa only [d,add_sub_right_comm] using h⟩

noncomputable def diameter {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  univ.sup fun x => univ.sup (G.dist x)
noncomputable def radius {U : Type*} [Fintype U] [Nonempty U] (G : SimpleGraph U) :=
  univ.inf' univ_nonempty fun x => univ.sup (G.dist x)
noncomputable def mean {U : Type*} [Fintype U] (G : SimpleGraph U) : ℚ :=
  ((∑ x : U, ∑ y : U, G.dist x y : ℕ) : ℚ) / (Fintype.card U * (Fintype.card U - 1) : ℕ)

theorem ecc (x : V) : univ.sup (C.dist x) = 21 := by
  have bound : ∀ p : V, len p ≤ 21 := by decide
  apply le_antisymm (Finset.sup_le fun y _ => (metric.2 x y).le.trans (bound _))
  have e : C.dist x (21+x) = 21 := by rw [metric.2,d,add_sub_cancel_right]; decide
  rw [← e]
  exact Finset.le_sup (f:=C.dist x) (mem_univ _)

theorem diameter43 : diameter C = 21 := by
  simp only [diameter,ecc]
  apply le_antisymm (Finset.sup_le (by simp)) (Finset.le_sup (f:=fun _ : V => 21) (mem_univ 0))
theorem radius43 : radius C = 21 := by simp [radius,ecc]

theorem mean43 : mean C = 11 := by
  have sumLen : ∑ z : V, len z = 462 := by decide
  have row (x : V) : ∑ y : V, C.dist x y = 462 := by
    simp only [metric.2,d]
    let e : V ≃ V := ⟨fun y => y-x, fun z => z+x,fun y => sub_add_cancel y x,fun z => add_sub_cancel_right z x⟩
    exact (e.sum_comp len).trans sumLen
  simp only [mean,row,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
  norm_num

theorem burning43 : burning C = 7 := by
  let f : Fin 7 → V := ![6, 18, 28, 36, 42, 3, 5]
  apply burning_certificate C d metric 7 f
  · decide
  · intro x r
    have cap : ∀ r : Fin 7, (univ.filter (fun z : V => len z ≤ r.val)).card ≤ 2*r.val+1 := by decide
    let e : V ≃ V := ⟨fun y => y-x,fun z => z+x,fun y => sub_add_cancel y x,fun z => add_sub_cancel_right z x⟩
    apply le_trans (Finset.card_le_card_of_injOn e ?_ e.injective.injOn) (cap r)
    exact fun _ h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
  · decide

theorem slater43 : slater C = 15 := by
  let l := List.replicate 43 2
  apply slater_certificate C l _ 15 (by decide) (by decide)
  unfold degreesDesc
  simp only [deg,Finset.val_univ_fin,Multiset.map_coe,Multiset.coe_sort]
  have h : (List.finRange 43).map (fun _ => 2) = List.replicate 43 2 := by decide
  rw [h]
  simp [l,List.mergeSort]

noncomputable def cover {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {k : ℕ | Gᶜ.Colorable k}

theorem cover43 : cover C = 22 := by
  let paint (v : V) : Fin 22 := ⟨v.val/2,by have := v.isLt; omega⟩
  have upper : Cᶜ.Colorable 22 := by
    have proper : ∀ x y : V, Cᶜ.Adj x y → paint x ≠ paint y := by decide
    exact ⟨Coloring.mk paint (fun h => proper _ _ h)⟩
  have att : Cᶜ.Colorable (cover C) := Nat.sInf_mem (s := {k | Cᶜ.Colorable k}) ⟨22,upper⟩
  obtain ⟨col⟩ := att
  have small (i : Fin (cover C)) : (univ.filter (fun x => col x = i)).card ≤ 2 := by
    by_contra! h
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp h
    have adj {u v : V} (ne : u ≠ v) (same : col u = col v) : C.Adj u v := by
      by_contra no
      exact col.valid ((compl_adj _ _ _).mpr ⟨ne,no⟩) same
    have h1 := (mem_filter.mp ha).2
    have h2 := (mem_filter.mp hb).2
    have h3 := (mem_filter.mp hc).2
    exact triangle a b c (adj ab (h1.trans h2.symm)) (adj bc (h2.trans h3.symm)) (adj ac.symm (h3.trans h1.symm))
  have count := Finset.card_eq_sum_card_fiberwise (s:=univ) (t:=univ) (f:=fun x : V => col x) (by simp)
  have cap := Finset.sum_le_sum (s:=univ) (fun i _ => small i)
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at count cap
  change 43 = ∑ i, (univ.filter (fun x : V => col x = i)).card at count
  have budget : 43 ≤ cover C * 2 := count.trans_le cap
  exact le_antisymm (Nat.sInf_le upper) (by omega)
end CycleBatch
