import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-!
# Written on the Wall II, Conjecture 111

For a connected graph let A be a maximum independent set and put a = |A|,
n = |V|, and s = sum_v (λ(v) - 1). Let q be the size of the union of the
neighbourhoods of the maximum-degree vertices in the complement.

The proof first establishes s ≥ a - 1. Retain every edge incident to A.
For a vertex v outside A, these edges go to an independent set of neighbours.
Choose a shortest-path parent p(v) towards a fixed root. If both endpoints
are outside A and share an A-neighbour, the parent edge can be replaced by a
two-edge walk through A. Otherwise retain that parent edge and charge it to v:
the vertex p(v) extends the independent set of neighbours in A. The retained
graph is connected and has at most sum_(v outside A) λ(v) edges.

Let x be the minimum size of a closed neighbourhood in the original graph,
t = n - q, and h the number of members of A with minimum closed degree.
The intersection of all minimum closed neighbourhoods has size t ≤ x.
If t = x those neighbourhoods are identical, so h ≤ 1. Double counting
closed-neighbourhood incidences with A gives ax + (a - h) ≤ n + s, and
excluding all but one member of A from any member's closed neighbourhood gives
q ≥ a - 1. The arithmetic lemma combines these facts into n(a - 2) < qs
when a ≥ 2. This is exactly the desired ceiling inequality. Singleton and
other a ≤ 1 cases are handled separately.

Source: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/
namespace Graffiti111

private theorem arithmetic (n a s q x t h : ℕ)
    (ha : 2 ≤ a) (han : a < n) (hx : 0 < x)
    (hs : a ≤ s + 1) (hq : a ≤ q + 1)
    (ht : t ≤ x) (htq : q + t = n)
    (hh : h ≤ a) (hfull : t = x → h ≤ 1)
    (hcount : a * x + (a - h) ≤ n + s) :
    n * (a - 2) < q * s := by
  have hcount' : a * x + a ≤ n + s + h := by omega
  have hcount'' : a * x ≤ n + s := by omega
  have ht' : t < x ∨ t = x := by omega
  have hcases : a ≤ s ∨ s = a - 1 := by omega
  rcases hcases with hlarge | hsmall
  · by_contra! fail
    have hprod : s < n := by
      by_contra! hns
      have p1 := Nat.mul_le_mul (show a - 1 ≤ q by omega) hns
      have p2 : n * (a - 2) < (a - 1) * n := by
        rw [Nat.mul_comm (a - 1) n]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    have hstep : a * t ≤ n + s := (Nat.mul_le_mul_left _ ht).trans hcount''
    have hfail' : n * (s - (a - 2)) ≤ t * s := by
      have z : (s - (a - 2)) + (a - 2) = s := by omega
      have z₁ := congrArg (n * ·) z
      have z₂ := congrArg (· * s) htq
      simp only [Nat.mul_add] at z₁
      simp only [Nat.add_mul] at z₂
      omega
    have z₁ := Nat.mul_le_mul_left a hfail'
    have z₂ := Nat.mul_le_mul_right s hstep
    have z₃ : 2 * s ≤ a * (s - (a - 2)) := by
      have z : s - (a - 2) = (s - a) + 2 := by omega
      rw [z, Nat.mul_add]
      have p := Nat.mul_le_mul_right (s - a) ha
      have e : (s - a) + a = s := by omega
      have E := congrArg (2 * ·) e
      simp only [Nat.mul_add] at E
      rw [Nat.mul_comm 2 a] at E
      omega
    have z₄ := Nat.mul_le_mul_right n z₃
    have last : (n + s) * s < 2 * s * n := by
      calc
        (n + s) * s < (n + n) * s := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        _ = 2 * s * n := by ring
    rw [Nat.mul_left_comm a n] at z₁
    have u : a * (s - (a - 2)) * n ≤ (n + s) * s := by
      calc
        _ = n * (a * (s - (a - 2))) := Nat.mul_comm ..
        _ ≤ a * (t * s) := z₁
        _ = (a * t) * s := (Nat.mul_assoc ..).symm
        _ ≤ _ := z₂
    omega
  · have hsmall' : s + 1 = a := by omega
    have hnt : s * t < n := by
      rcases ht' with hlt | heq
      · have p : s * t ≤ s * x := Nat.mul_le_mul_left _ ht
        have strict : s * x < a * x := Nat.mul_lt_mul_of_pos_right (by omega) hx
        have bound : s * t + s + x ≤ a * x := by
          calc
            _ = s * (t + 1) + x := by ring
            _ ≤ s * x + x := Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
            _ = a * x := by rw [← hsmall', Nat.add_mul, Nat.one_mul]
        omega
      · have h1 := hfull heq
        have p : s * t < a * x := by
          rw [heq]
          exact Nat.mul_lt_mul_of_pos_right (by omega) hx
        omega
    have z : (a - 2) + 1 = s := by omega
    have z₁ := congrArg (n * ·) z
    have z₂ := congrArg (· * s) htq
    simp only [Nat.mul_add, Nat.mul_one] at z₁
    simp only [Nat.add_mul] at z₂
    rw [Nat.mul_comm t s] at z₂
    omega


open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pairwise nonadjacency, including the empty set. -/
def Independent (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ (v w : V), v ∈ A → w ∈ A → ¬ G.Adj v w

noncomputable section
open Classical

omit [Fintype V] in
private lemma independent_insert {G : SimpleGraph V} {A : Finset V} {v : V}
    (hA : Independent G A) (hv : ∀ w ∈ A, ¬ G.Adj v w) :
    Independent G (insert v A) := by
  intro x y hx hy
  by_cases hxv : x = v
  · subst x
    rcases mem_insert.mp hy with rfl | hy
    · exact G.loopless _
    · exact hv _ hy
  · have hx' : x ∈ A := (mem_insert.mp hx).resolve_left hxv
    rcases mem_insert.mp hy with rfl | hy
    · exact fun ha => hv _ hx' ha.symm
    · exact hA _ _ hx' hy

omit [Fintype V] [DecidableEq V] in
private lemma parent_exists (G : SimpleGraph V) (hc : G.Connected) (r v : V)
    (hv : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.dist w r < G.dist v r := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact False.elim (hv rfl)
  | cons e q =>
    refine ⟨_, e, ?_⟩
    have hq := G.dist_le q
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

private lemma edge_count (F : V → Finset V) (K : SimpleGraph V)
    (h : ∀ v w, K.Adj v w → w ∈ F v ∨ v ∈ F w) :
    Nat.card K.edgeSet ≤ ∑ v, (F v).card := by
  classical
  let E := (univ.sigma F).image (fun p : Σ _ : V, V => s(p.1, p.2))
  have hsub : K.edgeFinset ⊆ E := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ v w =>
      have hadj : K.Adj v w := by simpa using he
      rcases h v w hadj with h₁ | h₂
      · exact mem_image.mpr ⟨⟨v,w⟩, by simp [h₁], rfl⟩
      · exact mem_image.mpr ⟨⟨w,v⟩, by simp [h₂], Sym2.eq_swap⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  exact (card_le_card hsub).trans (by simpa using (card_image_le (s := univ.sigma F)
    (f := fun p : Σ _ : V, V => s(p.1, p.2))))

private lemma local_budget (G : SimpleGraph V) (hc : G.Connected) (A : Finset V)
    (hA : Independent G A) (r : V)
    (S : V → ℕ) (hS : ∀ v (B : Finset V), Independent G B →
      (∀ w ∈ B, G.Adj v w) → B.card ≤ S v) :
    Fintype.card V ≤ (∑ v ∈ univ \ A, S v) + 1 := by
  classical
  let N (v : V) := A.filter (fun w => G.Adj v w)
  have memN (v w : V) : w ∈ N v ↔ w ∈ A ∧ G.Adj v w := mem_filter
  let p (v : V) : V :=
    if hv : v = r then r else Classical.choose (parent_exists G hc r v hv)
  have hp (v : V) (hv : v ≠ r) : G.Adj v (p v) ∧ G.dist (p v) r < G.dist v r := by
    simpa only [p, dif_neg hv] using Classical.choose_spec (parent_exists G hc r v hv)
  let F (v : V) :=
    if v ∈ A then ∅ else if v ≠ r ∧ p v ∉ A ∧ (∀ w ∈ N v, ¬ G.Adj (p v) w)
    then insert (p v) (N v) else N v
  have N_sub (v w : V) (h : w ∈ N v) : w ∈ A := ((memN ..).mp h).1
  have N_ind (v : V) : Independent G (N v) :=
    fun x y hx hy => hA x y (N_sub _ _ hx) (N_sub _ _ hy)
  have F_ind (v : V) : Independent G (F v) := by
    by_cases hv : v ∈ A
    · simp [F, hv, Independent]
    simp only [F, if_neg hv]
    split_ifs with h
    · exact independent_insert (N_ind v) h.2.2
    · exact N_ind v
  have F_adj (v w : V) (hm : w ∈ F v) : G.Adj v w := by
    by_cases hv : v ∈ A
    · simp [F, hv] at hm
    simp only [F, if_neg hv] at hm
    split_ifs at hm with h
    · rcases mem_insert.mp hm with rfl | hw
      · exact (hp v h.1).1
      · exact ((memN ..).mp hw).2
    · exact ((memN ..).mp hm).2
  let K : SimpleGraph V :=
    ⟨fun v w => w ∈ F v ∨ v ∈ F w,
      fun _ _ h => h.elim Or.inr Or.inl,
      fun v h => h.elim (fun hv => G.loopless v (F_adj v v hv))
        (fun hv => G.loopless v (F_adj v v hv))⟩
  have N_F (v w : V) (hv : v ∉ A) (hm : w ∈ N v) : w ∈ F v := by
    simp only [F, if_neg hv]
    split_ifs <;> simp [hm]
  have edgeA {v w : V} (ha : G.Adj v w) (hw : w ∈ A) : K.Adj v w := by
    have hv : v ∉ A := fun hv => hA _ _ hv hw ha
    exact Or.inl (N_F v w hv ((memN ..).mpr ⟨hw,ha⟩))
  have reach_parent (v : V) (hv : v ≠ r) : K.Reachable v (p v) := by
    have h := (hp v hv).1
    by_cases h1 : v ∈ A
    · exact (edgeA h.symm h1).symm.reachable
    by_cases h2 : p v ∈ A
    · exact (edgeA h h2).reachable
    by_cases h3 : ∀ w ∈ N v, ¬ G.Adj (p v) w
    · exact (show K.Adj v (p v) from Or.inl (by simpa only [F, if_neg h1, if_pos (show v ≠ r ∧ p v ∉ A ∧ (∀ w ∈ N v, ¬ G.Adj (p v) w) from ⟨hv, h2, h3⟩)] using (mem_insert_self (p v) (N v)))).reachable
    · push_neg at h3
      obtain ⟨w, hw, hw'⟩ := h3
      have hwa := N_sub v w hw
      exact (edgeA ((memN ..).mp hw).2 hwa).reachable.trans (edgeA hw' hwa).symm.reachable
  have rr (v : V) : K.Reachable v r := by
    induction v using (measure (fun v => G.dist v r)).wf.induction with
    | h v ih =>
      by_cases hv : v = r
      · subst v
        exact SimpleGraph.Reachable.refl r
      · exact (reach_parent v hv).trans (ih (p v) (hp v hv).2)
  letI : Nonempty V := ⟨r⟩
  have hK : K.Connected := ⟨fun v w => (rr v).trans (rr w).symm⟩
  have cap : ∑ v, (F v).card ≤ ∑ v ∈ univ \ A, S v := by
    rw [show univ \ A = univ.filter (fun v => v ∉ A) by ext; simp, sum_filter]
    refine sum_le_sum (fun v _ => ?_)
    by_cases hv : v ∈ A
    · simp [F, hv]
    · simp [hv]
      exact hS v (F v) (F_ind v) (F_adj v)
  have ed := edge_count F K (by intro v w h; exact h)
  simpa using hK.card_vert_le_card_edgeSet_add_one.trans (Nat.add_le_add_right (ed.trans cap) 1)


/-- The closed neighbourhood of a vertex in the original graph. -/
noncomputable def closedNbr (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter fun w => v = w ∨ G.Adj v w

private lemma mem_closedNbr (G : SimpleGraph V) (v w : V) :
    w ∈ closedNbr G v ↔ v = w ∨ G.Adj v w := by simp [closedNbr]

private lemma closed_symm {G : SimpleGraph V} {v w : V} :
    w ∈ closedNbr G v ↔ v ∈ closedNbr G w := by
  simp only [mem_closedNbr]
  exact or_congr eq_comm ⟨fun h => h.symm, fun h => h.symm⟩

/-- Set-neighbourhood in the complement of the vertices of minimum closed degree. -/
noncomputable def complementNbr (G : SimpleGraph V) : Finset V :=
  univ.filter fun w => ∃ v : V, (∀ u : V, (closedNbr G v).card ≤ (closedNbr G u).card) ∧
    w ∉ closedNbr G v

omit [DecidableEq V] in
private lemma local_one (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 ≤ Fintype.card V) (v : V) : ∃ w, G.Adj v w := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne v
  exact (parent_exists G hc w v (Ne.symm hw)).imp (fun _ h => h.1)

private lemma connected_count (G : SimpleGraph V) (hc : G.Connected) (A : Finset V)
    (hA : Independent G A) (ha : 2 ≤ A.card) (L : V → ℕ)
    (hL : ∀ v (B : Finset V), Independent G B →
      (∀ w ∈ B, G.Adj v w) → B.card ≤ L v) :
    Fintype.card V * (A.card - 2) <
      (complementNbr G).card * (∑ v, (L v - 1)) := by
  classical
  let n := Fintype.card V
  let a := A.card
  let s := ∑ v, (L v - 1)
  let Q := complementNbr G
  let T := univ \ Q
  let q := Q.card
  let t := T.card
  haveI : Nonempty V := hc.nonempty
  let r : V := Classical.choice ‹Nonempty V›
  have an : a ≤ n := card_le_univ A
  have hn : 2 ≤ n := ha.trans an
  have lpos (v : V) : 1 ≤ L v := by
    obtain ⟨w, hw⟩ := local_one G hc hn v
    simpa using hL v {w} (by
      intro x y hx hy
      simp at hx hy
      subst x; subst y
      exact G.loopless w) (by simpa using hw)
  have han : a < n := by
    by_contra! h
    have E : A = univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using h)
    obtain ⟨w, hw⟩ := local_one G hc hn r
    exact hA r w (by simp [E]) (by simp [E]) hw
  have hs : a ≤ s + 1 := by
    have BL := local_budget G hc A hA r L hL
    have bn : (univ \ A).card = n - a := by simp [n, a, card_sdiff (subset_univ A)]
    have BA : ∑ v ∈ univ \ A, L v =
        (univ \ A).card + ∑ v ∈ univ \ A, (L v - 1) := by
      calc
        _ = ∑ v ∈ univ \ A, (1 + (L v - 1)) :=
          sum_congr rfl (fun v _ => by have := lpos v; omega)
        _ = _ := by rw [sum_add_distrib]; simp
    have BU : ∑ v ∈ univ \ A, (L v - 1) ≤ s :=
      sum_le_sum_of_subset (subset_univ _)
    omega
  obtain ⟨v₀, _, hv₀⟩ := exists_min_image (univ : Finset V)
    (fun v => (closedNbr G v).card) ⟨r, mem_univ _⟩
  let x := (closedNbr G v₀).card
  have xmin (v : V) : x ≤ (closedNbr G v).card := hv₀ _ (mem_univ _)
  have hx : 0 < x := card_pos.mpr ⟨v₀, (mem_closedNbr ..).mpr (Or.inl rfl)⟩
  let M := A.filter fun v => (closedNbr G v).card = x
  let h := M.card
  have hh : h ≤ a := card_le_card (filter_subset ..)
  have htq : q + t = n := by
    have ht : t = n - q := by simp [t, T, n, q, card_sdiff (subset_univ Q)]
    have hqn : q ≤ n := card_le_univ Q
    omega
  have TK (v : V) (hm : (closedNbr G v).card = x) : T ⊆ closedNbr G v := by
    intro w hw
    apply Classical.byContradiction
    intro hnot
    have hQ : w ∈ Q := by
      exact mem_filter.mpr ⟨mem_univ _, v, fun u => hm ▸ xmin u, hnot⟩
    exact (mem_sdiff.mp hw).2 hQ
  have ht : t ≤ x := card_le_card (TK v₀ rfl)
  have hfull (he : t = x) : h ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    have U : T = closedNbr G u :=
      eq_of_subset_of_card_le (TK u (mem_filter.mp hu).2) (by rw [(mem_filter.mp hu).2, ← he])
    have W : T = closedNbr G v :=
      eq_of_subset_of_card_le (TK v (mem_filter.mp hv).2) (by rw [(mem_filter.mp hv).2, ← he])
    have hmem : v ∈ closedNbr G u := by
      rw [← U, W]
      exact (mem_closedNbr ..).mpr (Or.inl rfl)
    exact ((mem_closedNbr ..).mp hmem).resolve_right
      (hA _ _ (mem_filter.mp hu).1 (mem_filter.mp hv).1)
  have hq : a ≤ q + 1 := by
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < A.card by omega)
    have hsub : A.erase v ⊆ univ \ closedNbr G v := by
      intro w hw
      have ⟨hwv, hwA⟩ := mem_erase.mp hw
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      exact fun hz => ((mem_closedNbr ..).mp hz).elim (fun e => hwv e.symm) (hA _ _ hv hwA)
    have cc := card_le_card hsub
    rw [card_erase_of_mem hv, card_sdiff (subset_univ _), card_univ] at cc
    have xv := xmin v
    change a - 1 ≤ n - (closedNbr G v).card at cc
    omega
  have hcount : a * x + (a - h) ≤ n + s := by
    have b : a * x + (a - h) ≤ ∑ v ∈ A, (closedNbr G v).card := by
      have eq : (∑ v ∈ A, (x + if (closedNbr G v).card = x then 0 else 1)) =
          a * x + (a - h) := by
        rw [sum_add_distrib, sum_const_nat (fun _ _ => rfl)]
        have E : (∑ v ∈ A, (if (closedNbr G v).card = x then 0 else 1)) =
            ∑ v ∈ A, (if ¬ (closedNbr G v).card = x then 1 else 0) := by
          refine sum_congr rfl (fun _ _ => ?_)
          split_ifs <;> rfl
        rw [E, ← sum_filter]
        have e : A.filter (fun v => ¬ (closedNbr G v).card = x) = A \ M := by
          ext v
          simp only [M, mem_filter, mem_sdiff]
          tauto
        rw [e]
        simp [a, h, M, card_sdiff (filter_subset ..)]
      rw [← eq]
      refine sum_le_sum (fun v _ => ?_)
      have hv := xmin v
      split_ifs <;> omega
    have e (v : V) : (closedNbr G v).card =
        ∑ w : V, (if w ∈ closedNbr G v then 1 else 0) := by
      rw [← sum_filter]
      simp
    have cross (w : V) : (∑ v ∈ A, (if w ∈ closedNbr G v then 1 else 0)) =
        (A.filter (fun v => v ∈ closedNbr G w)).card := by
      calc
        _ = ∑ v ∈ A, (if v ∈ closedNbr G w then 1 else 0) := by
          refine sum_congr rfl (fun v _ => ?_)
          simp only [show w ∈ closedNbr G v ↔ v ∈ closedNbr G w from closed_symm]
        _ = _ := by rw [← sum_filter]; simp
    have cap (w : V) : (A.filter (fun v => v ∈ closedNbr G w)).card ≤ 1 + (L w - 1) := by
      let B := A.filter (fun v => v ∈ closedNbr G w)
      change B.card ≤ _
      by_cases hw : w ∈ A
      · have sub : B ⊆ {w} := by
          intro v hv
          obtain ⟨hv, hc⟩ := mem_filter.mp hv
          exact mem_singleton.mpr (((mem_closedNbr ..).mp hc).resolve_right (hA _ _ hw hv)).symm
        have i := card_le_card sub
        simp at i
        omega
      · have hi : Independent G B :=
          fun u v hu hv => hA _ _ (mem_filter.mp hu).1 (mem_filter.mp hv).1
        have adj (v : V) (hv : v ∈ B) : G.Adj w v :=
          ((mem_closedNbr ..).mp (mem_filter.mp hv).2).resolve_left
            (fun he => hw (he ▸ (mem_filter.mp hv).1))
        have b := hL w B hi adj
        have pos := lpos w
        omega
    refine b.trans ?_
    simp_rw [e]
    rw [sum_comm]
    simp_rw [cross]
    have bound := sum_le_sum (fun w (_ : w ∈ (univ : Finset V)) => cap w)
    simpa [sum_add_distrib, n, s] using bound
  exact arithmetic n a s q x t h ha han hx hs hq ht htq hh hfull hcount


/-- Maximum cardinality of an independent set within a vertex set. -/
def independenceIn (G : SimpleGraph V) (W : Finset V) : ℕ :=
  (W.powerset.filter (Independent G)).sup Finset.card

/-- Independence number of a graph. -/
def independence (G : SimpleGraph V) : ℕ := independenceIn G univ

/-- Independence number in the open neighbourhood of a vertex. -/
def localIndependence (G : SimpleGraph V) (v : V) : ℕ :=
  independenceIn G (univ.filter fun w => G.Adj v w)

omit [Fintype V] [DecidableEq V] in
private lemma independenceIn_upper (G : SimpleGraph V) (W B : Finset V)
    (hb : B ⊆ W) (hi : Independent G B) : B.card ≤ independenceIn G W :=
  le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hb, hi⟩)

omit [Fintype V] [DecidableEq V] in
private lemma independenceIn_attained (G : SimpleGraph V) (W : Finset V) :
    ∃ B, B ⊆ W ∧ Independent G B ∧ B.card = independenceIn G W := by
  let H := W.powerset.filter (Independent G)
  have he : ∅ ∈ H := by simp [H, Independent]
  obtain ⟨B, hB, hm⟩ := exists_max_image H Finset.card ⟨∅, he⟩
  obtain ⟨hBW, hBI⟩ := mem_filter.mp hB
  refine ⟨B, mem_powerset.mp hBW, hBI, le_antisymm (le_sup (f := card) hB) ?_⟩
  exact Finset.sup_le_iff.mpr hm

omit [DecidableEq V] in
private lemma local_upper (G : SimpleGraph V) (v : V) (B : Finset V)
    (hi : Independent G B) (hb : ∀ w ∈ B, G.Adj v w) :
    B.card ≤ localIndependence G v :=
  independenceIn_upper G _ B (fun w hw => mem_filter.mpr ⟨mem_univ _, hb w hw⟩) hi

/-- Complement neighbourhood with maximum complement degree stated in Mathlib terms. -/
theorem mem_complementNbr (G : SimpleGraph V) (w : V) :
    w ∈ complementNbr G ↔ ∃ v : V,
      (∀ u : V, (Gᶜ.neighborFinset u).card ≤ (Gᶜ.neighborFinset v).card) ∧ Gᶜ.Adj v w := by
  classical
  have E (v u : V) : u ∉ closedNbr G v ↔ Gᶜ.Adj v u := by
    simp [mem_closedNbr, SimpleGraph.compl_adj, not_or]
  have N (v : V) : univ \ closedNbr G v = Gᶜ.neighborFinset v := by
    ext u
    simpa only [mem_sdiff, mem_univ, true_and, SimpleGraph.mem_neighborFinset] using E v u
  have nc (v : V) : (Gᶜ.neighborFinset v).card =
      Fintype.card V - (closedNbr G v).card := by
    simp [← N, card_sdiff (subset_univ _)]
  simp only [complementNbr, mem_filter, mem_univ, true_and, E, nc]
  refine exists_congr (fun v => and_congr_left' ⟨?_, ?_⟩)
  · intro h u
    exact Nat.sub_le_sub_left (h u) _
  · intro h u
    have h₁ := h u
    have h₂ := card_le_univ (closedNbr G u)
    have h₃ := card_le_univ (closedNbr G v)
    omega

/-- Graffiti.pc / Written on the Wall II, Conjecture 111. -/
theorem conjecture111 (G : SimpleGraph V) (hc : G.Connected) :
    (independence G : ℤ) ≤ ⌈(1 : ℚ) + (complementNbr G).card *
      ((∑ v, ((localIndependence G v : ℚ) - 1)) / Fintype.card V)⌉ := by
  classical
  letI : Nonempty V := hc.nonempty
  let n := Fintype.card V
  let q := (complementNbr G).card
  let a := independence G
  let s := ∑ v, (localIndependence G v - 1)
  have hn : 0 < n := Fintype.card_pos
  obtain ⟨A, _, hi, hA⟩ := independenceIn_attained G univ
  change A.card = a at hA
  change (a : ℤ) ≤ ⌈(1 : ℚ) + (q : ℚ) *
    ((∑ v, ((localIndependence G v : ℚ) - 1)) / (n : ℚ))⌉
  by_cases h : 2 ≤ n
  · have lp (v : V) : 1 ≤ localIndependence G v := by
      obtain ⟨w, hw⟩ := local_one G hc h v
      simpa using local_upper G v {w} (by
        intro x y hx hy
        simp at hx hy
        subst x; subst y
        exact G.loopless w) (by simpa using hw)
    have eq : (∑ v, ((localIndependence G v : ℚ) - 1)) = (s : ℚ) := by
      rw [show s = ∑ v, (localIndependence G v - 1) from rfl, Nat.cast_sum]
      exact sum_congr rfl (fun v _ => by rw [Nat.cast_sub (lp v), Nat.cast_one])
    rw [eq]
    have hp : 0 < (n : ℚ) := by exact_mod_cast hn
    by_cases ha : 2 ≤ a
    · have hprod := connected_count G hc A hi (hA ▸ ha)
        (localIndependence G) (local_upper G)
      change n * (A.card - 2) < q * s at hprod
      rw [hA] at hprod
      have hcast : (n : ℚ) * ((a : ℚ) - 2) < (q : ℚ) * (s : ℚ) := by
        have f : ((n * (a - 2) : ℕ) : ℚ) < ((q * s : ℕ) : ℚ) := by exact_mod_cast hprod
        simpa only [Nat.cast_mul, Nat.cast_sub ha, Nat.cast_ofNat] using f
      have hd : (a : ℚ) - 2 < (q : ℚ) * (s : ℚ) / n :=
        (lt_div_iff₀ hp).mpr (by rwa [mul_comm])
      apply Int.le_ceil_iff.mpr
      push_cast
      rw [← mul_div_assoc]
      linarith
    · have hnonneg : 0 ≤ (q : ℚ) * ((s : ℚ) / (n : ℚ)) := by positivity
      have B : (1 : ℤ) ≤ ⌈(1 : ℚ) + (q : ℚ) * ((s : ℚ) / (n : ℚ))⌉ := by
        apply Int.le_ceil_iff.mpr
        norm_num
        linarith
      exact (show (a : ℤ) ≤ 1 by omega).trans B
  · have hn1 : Fintype.card V = 1 := by change n = 1; omega
    haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn1.le
    have q0 : q = 0 := by
      change (complementNbr G).card = 0
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_not_mem.mpr
      intro w hw
      obtain ⟨v, _, hbad⟩ := (mem_complementNbr G w).mp hw
      exact hbad.ne (Subsingleton.elim ..)
    have a1 : a ≤ 1 := by rw [← hA, ← hn1]; exact card_le_univ A
    simp only [q0, Nat.cast_zero, zero_mul, add_zero, Int.ceil_one]
    exact_mod_cast a1

#print axioms conjecture111

end
end Graffiti111
