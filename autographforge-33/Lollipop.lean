import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

/-! AutoGraphForge normalized row 33, ID fe71fb58. A clique with a long pendant path. -/
namespace Lollipop
open Finset SimpleGraph
open scoped BigOperators
set_option maxHeartbeats 3200000
set_option maxRecDepth 16384

/-- Published ball-cover definition from the row 66 formalization. -/
def Burns {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ source : Fin k → U, ∀ v, ∃ t : Fin k, ∃ p : G.Walk (source t) v,
    p.length ≤ k - 1 - t.val

noncomputable def burning {U : Type*} (G : SimpleGraph U) : ℕ := sInf {k | Burns G k}

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  sInf {t | Fintype.card U ≤ t + ((degreesDesc G).take t).sum}

private theorem sum_widths (k : ℕ) : (∑ i : Fin k, (2 * (k-1-i.val)+1)) = k*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.succ_sub_one,Nat.sub_zero]
    have shift (i : Fin k) : k - (i.val+1) = k-1-i.val := by omega
    simp_rw [shift,ih]
    simp [Nat.succ_mul,Nat.mul_succ]
    omega

/-- A radius-r source reaches at most 2r+1 different integer levels. -/
theorem height_bound {U : Type*} {G : SimpleGraph U} (h : U → ℕ)
    (edge : ∀ {x y}, G.Adj x y → h x ≤ h y + 1)
    {N : ℕ} (hits : ∀ i < N, ∃ v, h v = i) {k : ℕ} (burns : Burns G k) : N ≤ k*k := by
  obtain ⟨src,covers⟩ := burns
  have along {x y} (p : G.Walk x y) : h x ≤ h y+p.length ∧ h y ≤ h x+p.length := by
    induction p with
    | nil => simp
    | cons e p ih =>
      have fw := edge e
      have bw := edge e.symm
      simp only [Walk.length_cons]
      omega
  let rad (i : Fin k) := k-1-i.val
  let interval (i : Fin k) := Icc (h (src i) - rad i) (h (src i) + rad i)
  have sub : range N ⊆ univ.biUnion interval := by
    intro l hl
    obtain ⟨v,rfl⟩ := hits l (mem_range.mp hl)
    obtain ⟨i,p,dist⟩ := covers v
    have bound := along p
    apply mem_biUnion.mpr ⟨i,mem_univ _,?_⟩
    apply mem_Icc.mpr
    dsimp [rad]
    omega
  have cap (i : Fin k) : (interval i).card ≤ 2*rad i+1 := by
    simp only [interval,Nat.card_Icc]
    omega
  calc N = (range N).card := (card_range _).symm
       _ ≤ (univ.biUnion interval).card := card_le_card sub
       _ ≤ ∑ i : Fin k, (interval i).card := card_biUnion_le
       _ ≤ ∑ i : Fin k, (2*rad i+1) := sum_le_sum (fun i _ => cap i)
       _ = k*k := sum_widths k

/-- Clique on the first n+2 labels, with the remaining n+2 labels forming its tail. -/
abbrev V (n : ℕ) := Fin ((n+2)*2)

def graph (n : ℕ) : SimpleGraph (V n) where
  Adj x y := (x.val<n+2 ∧ y.val<n+2 ∧ x≠y) ∨ x.val+1=y.val ∨ y.val+1=x.val
  symm := by rintro x y (⟨hx,hy,ne⟩ | e | e)
             · exact Or.inl ⟨hy,hx,Ne.symm ne⟩
             · exact Or.inr (Or.inr e)
             · exact Or.inr (Or.inl e)
  loopless := by intro x; simp

instance (n : ℕ) : DecidableRel (graph n).Adj := fun x y =>
  inferInstanceAs (Decidable ((x.val<n+2 ∧ y.val<n+2 ∧ x≠y) ∨ x.val+1=y.val ∨ y.val+1=x.val))

theorem connected (n : ℕ) : (graph n).Connected := by
  have reach (j : ℕ) (hj : j < (n+2)*2) : (graph n).Reachable 0 ⟨j,hj⟩ := by
    induction j with
    | zero => exact .refl _
    | succ j ih =>
      have e : (graph n).Adj ⟨j,by omega⟩ ⟨j+1,hj⟩ := Or.inr (Or.inl rfl)
      exact (ih (by omega)).trans e.reachable
  exact ⟨fun x y => (reach x.val x.isLt).symm.trans (reach y.val y.isLt)⟩

theorem lollipop_height (n : ℕ) : n+4 ≤ burning (graph n) * burning (graph n) := by
  have feasible : Burns (graph n) ((n+2)*2) := ⟨id,fun v => ⟨v,.nil,by simp⟩⟩
  apply height_bound (G := graph n) (fun v => v.val-n) _ _
    (Nat.sInf_mem (show {k | Burns (graph n) k}.Nonempty from ⟨_,feasible⟩))
  · rintro x y (⟨hx,hy,_⟩ | h | h) <;> dsimp only <;> omega
  · intro i hi
    exact ⟨⟨i+n,by omega⟩,by simp⟩

private theorem two_largest {L : List ℕ} (d : ℕ) (sorted : L.Pairwise (· ≥ ·))
    (high : 2 ≤ (L.filter (fun x => decide (d ≤ x))).length) : 2*d ≤ (L.take 2).sum := by
  cases L with
  | nil => simp at high
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases ha : d ≤ a <;> simp [ha] at high
    | cons b tail =>
      obtain ⟨head,rest⟩ := List.pairwise_cons.mp sorted
      have ab := head b (by simp)
      have db : d ≤ b := by
        by_contra! small
        have allsmall : ∀ x ∈ b::tail, ¬ d ≤ x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | h
          · omega
          · have := (List.pairwise_cons.mp rest).1 x h
            omega
        have empty : (b::tail).filter (fun x => decide (d ≤ x)) = [] := by
          simpa [List.filter_eq_nil_iff] using allsmall
        by_cases ha : d ≤ a <;> simp [List.filter_cons,ha,empty] at high
      simp
      omega

theorem slater_le_two (n : ℕ) : slater (graph n) ≤ 2 := by
  let emb : Fin (n+2) ↪ V n := ⟨fun x => ⟨x.val,by omega⟩,fun _ _ eq => Fin.ext (congrArg (fun v : V n => v.val) eq)⟩
  let C := univ.map emb
  have core (x : V n) (hx : x ∈ C) : x.val < n+2 := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact i.isLt
  have high (x : V n) (hx : x ∈ C) : n+1 ≤ (graph n).degree x := by
    have sub : C.erase x ⊆ (graph n).neighborFinset x := by
      intro y hy
      obtain ⟨ne,hy⟩ := mem_erase.mp hy
      exact (mem_neighborFinset _ _ _).mpr (Or.inl ⟨core _ hx,core _ hy,Ne.symm ne⟩)
    have h := card_le_card sub
    simpa [C,card_erase_of_mem hx] using h
  let degrees := univ.val.map (fun x => (graph n).degree x)
  let L := degrees.sort (· ≥ ·)
  have sub : C ⊆ univ.filter (fun x => n+1 ≤ (graph n).degree x) :=
    fun x hx => mem_filter.mpr ⟨mem_univ _,high x hx⟩
  have count := card_le_card sub
  have many : 2 ≤ (L.filter (fun x => decide (n+1 ≤ x))).length := by
    have eq : (L.filter (fun x => decide (n+1 ≤ x))).length =
        (univ.filter (fun x => n+1 ≤ (graph n).degree x)).card := by
      change Multiset.card (Multiset.filter (fun x => n+1 ≤ x) (↑L : Multiset ℕ)) = _
      rw [Multiset.sort_eq,Multiset.filter_map,Multiset.card_map]
      rfl
    rw [eq]
    simp [C] at count
    omega
  have bound := two_largest (n+1) (Multiset.sort_sorted _ degrees) many
  change 2*(n+1) ≤ (L.take 2).sum at bound
  apply Nat.sInf_le (s := {t | Fintype.card (V n) ≤ t + ((degreesDesc (graph n)).take t).sum})
  change Fintype.card (Fin ((n+2)*2)) ≤ 2+(L.take 2).sum
  rw [Fintype.card_fin]
  omega

private theorem degree_gap (n : ℕ) (x : V n) : (graph n).degree x + 1 < (n+2)*2 := by
  have missed : ∃ y : V n, y ≠ x ∧ ¬(graph n).Adj x y := by
    by_cases hx : x.val < n+2
    · let y : V n := ⟨(n+2)*2-1,by omega⟩
      refine ⟨y,fun eq => ?_,?_⟩
      · have := congrArg Fin.val eq
        dsimp [y] at this
        omega
      · rintro (⟨_,hy,_⟩ | e | e) <;> dsimp [y] at * <;> omega
    · refine ⟨0,fun eq => ?_,?_⟩
      · subst x
        simp at hx
      · rintro (⟨hy,_,_⟩ | e | e) <;> simp at * <;> omega
  obtain ⟨y,ne,nonedge⟩ := missed
  have sub : insert x ((graph n).neighborFinset x) ⊆ univ.erase y := by
    intro w hw
    apply mem_erase.mpr ⟨?_,mem_univ _⟩
    rintro rfl
    obtain rfl | h := mem_insert.mp hw
    · exact ne rfl
    · exact nonedge ((mem_neighborFinset _ _ _).mp h)
  have cap := card_le_card sub
  rw [card_insert_of_not_mem (by simp),card_erase_of_mem (mem_univ y),card_univ,Fintype.card_fin] at cap
  rw [card_neighborFinset_eq_degree] at cap
  omega

theorem slater_exact (n : ℕ) : slater (graph n) = 2 := by
  apply Nat.le_antisymm (slater_le_two n)
  let L := degreesDesc (graph n)
  let N := (n+2)*2
  let costs : Set ℕ := {t | N ≤ t+(L.take t).sum}
  have eq : slater (graph n) = sInf costs := by
    simp [slater,costs,L,N,V]
  rw [eq]
  have feasible : N ∈ costs := by change N ≤ N+_; omega
  have min_ok := Nat.sInf_mem (show costs.Nonempty from ⟨N,feasible⟩)
  change N ≤ sInf costs+(L.take (sInf costs)).sum at min_ok
  by_contra! low
  rcases (show sInf costs=0 ∨ sInf costs=1 by omega) with h | h
  · simp [h,N] at min_ok
  · rw [h] at min_ok
    cases list : L with
    | nil => simp [list,N] at min_ok; omega
    | cons a tail =>
      have mem : a ∈ L := by simp [list]
      obtain ⟨x,_,hx⟩ := Multiset.mem_map.mp ((Multiset.mem_sort (· ≥ ·)).mp mem)
      have cap := degree_gap n x
      change (graph n).degree x = a at hx
      simp [list,N] at min_ok
      omega

/-- A four-source schedule on the sixteen-vertex witness, checked as actual walks. -/
private def within : ℕ → V 6 → V 6 → Bool
  | 0, u, v => decide (u = v)
  | r+1, u, v => decide (u = v ∨ ∃ w, (graph 6).Adj u w ∧ within r w v = true)

private theorem walk_of_within {r : ℕ} {u v : V 6} (h : within r u v = true) :
    ∃ p : (graph 6).Walk u v, p.length ≤ r := by
  induction r generalizing u v with
  | zero =>
    obtain rfl : u=v := of_decide_eq_true h
    exact ⟨.nil,by simp⟩
  | succ r ih =>
    change decide (_ ∨ _) = true at h
    rcases of_decide_eq_true h with rfl | ⟨w,uw,hit⟩
    · exact ⟨.nil,by simp⟩
    · obtain ⟨p,le⟩ := ih hit
      exact ⟨.cons uw p,by simpa using le⟩

theorem witness_burning : burning (graph 6) = 4 := by
  let src (i : Fin 4) : V 6 := if i=0 then 10 else if i=1 then 13 else if i=2 then 7 else 0
  have covers : ∀ v : V 6, ∃ i : Fin 4, within (3-i.val) (src i) v = true := by decide
  have feasible : Burns (graph 6) 4 := by
    refine ⟨src,fun v => ?_⟩
    obtain ⟨i,hit⟩ := covers v
    exact ⟨i,walk_of_within hit⟩
  apply Nat.le_antisymm (Nat.sInf_le (s := {k | Burns (graph 6) k}) feasible)
  change 4 ≤ burning (graph 6)
  by_contra! bad
  have cap : burning (graph 6) ≤ 3 := by omega
  have := Nat.mul_le_mul cap cap
  have := lollipop_height 6
  omega

theorem separation (B : ℕ) : ∃ n, (graph n).Connected ∧ slater (graph n) = 2 ∧ B < burning (graph n) := by
  refine ⟨B*B,connected _,slater_exact _,?_⟩
  have h := lollipop_height (B*B)
  by_contra! le
  have := Nat.mul_le_mul le le
  omega

theorem row33_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.Connected → burning G ≤ slater G + 1) := by
  intro claim
  have hb := claim (V 6) (graph 6) (by decide) (connected 6)
  rw [witness_burning,slater_exact] at hb
  omega

#print axioms height_bound
#print axioms slater_exact
#print axioms witness_burning
#print axioms lollipop_height
#print axioms separation
#print axioms row33_false
end Lollipop
