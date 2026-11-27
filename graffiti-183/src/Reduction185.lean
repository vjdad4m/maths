import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Metric reduction for Written on the Wall II #185. -/

namespace Graffiti185

open SimpleGraph Finset
open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V]

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl


def squareMaxDegree (G : SimpleGraph V) : ℕ := by
  classical
  exact (square G).maxDegree

def squareNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (square G).neighborFinset v

def maxLeaves (G : SimpleGraph V) : ℕ := by
  classical
  exact sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    (univ.filter (fun v => T.degree v = 1)).card = k}

def bipartiteNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter (fun s : Finset V =>
    ∃ c : s → Bool, ∀ a b : s, G.Adj a.val b.val → c a ≠ c b)).sup Finset.card

omit [Fintype V] in
private theorem le_square (G : SimpleGraph V) : G ≤ square G :=
  fun _ _ h => ⟨h.ne, le_trans (G.dist_le h.toWalk) (by simp [Adj.toWalk])⟩

omit [Fintype V] in
private theorem square_connected {G : SimpleGraph V} (hc : G.Connected) :
    (square G).Connected := hc.mono (le_square G)

omit [Fintype V] in
private theorem dist_le_twice_square_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : (square G).Walk v w) : G.dist v w ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h' : G.dist a b ≤ 2 := h.2
    have htri : G.dist a c ≤ G.dist a b + G.dist b c := hc.dist_triangle
    rw [Walk.length_cons]
    omega

omit [Fintype V] in
private theorem square_dist_le_half_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : G.Walk v w) : (square G).dist v w ≤ (p.length + 1) / 2 := by
  match p with
  | .nil => simp
  | .cons h .nil =>
    simpa [Adj.toWalk] using (square G).dist_le ((le_square G h).toWalk)
  | @Walk.cons _ _ a b c h (.cons (v := d) h' q) =>
    have htail := square_dist_le_half_walk hc q
    have hab : G.dist a b ≤ 1 := G.dist_le h.toWalk
    have hbd : G.dist b d ≤ 1 := G.dist_le h'.toWalk
    have had₀ : G.dist a d ≤ G.dist a b + G.dist b d := hc.dist_triangle
    have had : (square G).dist a d ≤ 1 := by
      by_cases heq : a = d
      · simp [heq, dist_self]
      · exact (square G).dist_le (show (square G).Adj a d from ⟨heq, by omega⟩).toWalk
    have htri : (square G).dist a c ≤ (square G).dist a d + (square G).dist d c :=
      (square_connected hc).dist_triangle
    simp only [Walk.length_cons]
    omega
termination_by p.length
decreasing_by simp only [Walk.length_cons]; omega

omit [Fintype V] in
theorem square_dist {G : SimpleGraph V} (hc : G.Connected) (v w : V) :
    (square G).dist v w = (G.dist v w + 1) / 2 := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  obtain ⟨q, hq⟩ := (square_connected hc).exists_walk_length_eq_dist v w
  have hlo := dist_le_twice_square_walk hc q
  have hhi := square_dist_le_half_walk hc p
  omega

/-- Sum of distances over all ordered pairs of the given set. Diagonals have
distance zero, so the sum is unchanged by dropping them. -/
def pairSum (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ S, G.dist x y

def distinctPairs (V : Type*) [Fintype V] : Finset (V × V) := by
  classical
  exact (univ : Finset V).offDiag

def averageDistance (G : SimpleGraph V) : ℚ :=
  (pairSum G univ : ℚ) / (distinctPairs V).card

def Claim185 (G : SimpleGraph V) : Prop :=
  (squareMaxDegree G : ℚ) + 2 * averageDistance (square G) ≤
    (maxLeaves G : ℚ) + (bipartiteNumber G : ℚ)

theorem distinctPairs_card (V : Type*) [Fintype V] :
    (distinctPairs V).card = Fintype.card V * (Fintype.card V - 1) := by
  classical
  rw [distinctPairs, offDiag_card, card_univ, Nat.mul_sub, Nat.mul_one]

theorem pairSum_eq_distinct_sum (G : SimpleGraph V) :
    pairSum G univ = ∑ p ∈ distinctPairs V, G.dist p.1 p.2 := by
  classical
  unfold pairSum
  rw [← Finset.sum_product (f := fun p : V × V => G.dist p.1 p.2)]
  apply Eq.symm
  apply sum_subset
  · intro p hp
    simp
  · intro ⟨x,y⟩ _ hy
    have hxy : x = y := by simpa [distinctPairs, Finset.mem_offDiag] using hy
    simp [hxy, dist_self]

theorem claim185_cross_multiply {G : SimpleGraph V} [Nontrivial V] :
    Claim185 G ↔
      squareMaxDegree G * (distinctPairs V).card + 2 * pairSum (square G) univ ≤
        (maxLeaves G + bipartiteNumber G) * (distinctPairs V).card := by
  have hp : (0 : ℚ) < ((distinctPairs V).card : ℚ) := by
    have hn : 1 < Fintype.card V := Fintype.one_lt_card
    have hpos : 0 < (distinctPairs V).card := by
      rw [distinctPairs_card]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hpos
  unfold Claim185 averageDistance
  rw [← mul_div_assoc, ← le_sub_iff_add_le', div_le_iff₀ hp, sub_mul, le_sub_iff_add_le]
  rw [add_comm, add_mul]
  norm_cast
  simp [Nat.add_mul]

omit [Fintype V] in
private theorem pairSum_insert {G : SimpleGraph V} [DecidableEq V]
    {x : V} {S : Finset V} (hx : x ∉ S) :
    pairSum G (insert x S) = pairSum G S + 2 * ∑ y ∈ S, G.dist x y := by
  unfold pairSum
  rw [sum_insert hx, sum_insert hx, dist_self, zero_add]
  simp_rw [sum_insert hx, sum_add_distrib]
  simp_rw [show ∀ y : V, G.dist y x = G.dist x y from fun _ => G.dist_comm]
  omega

private theorem choose_boundary_edge {G : SimpleGraph V} (hc : G.Connected)
    {S : Finset V} (hs : S.Nonempty) (hn : S.card < Fintype.card V) :
    ∃ x ∉ S, ∃ y ∈ S, G.Adj x y := by
  classical
  obtain ⟨u, hu⟩ := hs
  obtain ⟨w, _, hw⟩ := exists_mem_not_mem_of_card_lt_card (by rwa [card_univ] : S.card < (univ : Finset V).card)
  obtain ⟨p⟩ := hc.preconnected u w
  obtain ⟨d, _, h₁, h₂⟩ := p.exists_boundary_dart (S : Set V) hu hw
  exact ⟨d.snd, h₂, d.fst, h₁, d.adj.symm⟩

omit [Fintype V] in
private theorem insert_preserves_distance_bound {G : SimpleGraph V} [DecidableEq V]
    (hc : G.Connected) {S : Finset V} {x y : V} (hy : y ∈ S) (hxy : G.Adj x y)
    {k : ℕ} (hd : ∀ a ∈ S, ∀ b ∈ S, G.dist a b ≤ 4 + k) :
    ∀ a ∈ insert x S, ∀ b ∈ insert x S, G.dist a b ≤ 4 + (k + 1) := by
  intro a ha b hb
  have ht : ∀ u ∈ S, G.dist x u ≤ 4 + (k+1) := by
    intro u hu
    have h₁ : G.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
    have h₂ := hd y hy u hu
    have h₃ : G.dist x u ≤ G.dist x y + G.dist y u := hc.dist_triangle
    omega
  rcases mem_insert.mp ha with he | ha
  · subst a
    rcases mem_insert.mp hb with he | hb
    · subst b
      simp [dist_self]
    · exact ht b hb
  · rcases mem_insert.mp hb with he | hb
    · subst b
      rw [G.dist_comm]
      exact ht a ha
    · exact (hd a ha b hb).trans (by omega)

omit [Fintype V] in
private theorem row_bound {G : SimpleGraph V} [DecidableEq V] {S : Finset V}
    {x y : V} (hy : y ∈ S) (hxy : G.Adj x y) {r : ℕ}
    (hd : ∀ z ∈ S, G.dist x z ≤ r) (hr : 1 ≤ r) :
    (∑ z ∈ S, G.dist x z) + (r - 1) ≤ r * S.card := by
  have h₁ : G.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
  have he := sum_erase_add S (G.dist x) hy
  have hs : (∑ z ∈ S.erase y, G.dist x z) ≤ (S.erase y).card * r := by
    calc
      _ ≤ ∑ _z ∈ S.erase y, r :=
        sum_le_sum (fun z hz => hd z (mem_of_mem_erase hz))
      _ = _ := by simp
  have hcard := card_erase_add_one hy
  rw [← hcard, Nat.mul_add, Nat.mul_one]
  rw [mul_comm] at hs
  omega

private theorem step {G : SimpleGraph V} [DecidableEq V]
    (hc : G.Connected) {S : Finset V} (hs : S.Nonempty) (hn : S.card < Fintype.card V)
    {k : ℕ} (hd : ∀ a ∈ S, ∀ b ∈ S, G.dist a b ≤ 4 + k) :
    ∃ S' : Finset V, S ⊆ S' ∧ S'.card = S.card + 1 ∧
      (∀ a ∈ S', ∀ b ∈ S', G.dist a b ≤ 4 + (k+1)) ∧
      pairSum (square G) S' + 2 * (((k+6)/2) - 1) ≤
        pairSum (square G) S + 2 * ((k+6)/2) * S.card := by
  obtain ⟨x,hx,y,hy,hxy⟩ := choose_boundary_edge hc hs hn
  let T := insert x S
  have hT := insert_preserves_distance_bound hc hy hxy hd
  refine ⟨T, subset_insert _ _, card_insert_of_not_mem hx, hT, ?_⟩
  have hr : 1 ≤ (k+6)/2 := by omega
  have hxT : x ∈ T := mem_insert_self x _
  have hrow := row_bound hy (le_square G hxy) (r := (k+6)/2) (fun z hz => by
    have hp := hT x hxT z (mem_insert_of_mem hz)
    rw [square_dist hc]
    omega) hr
  change pairSum (square G) (insert x S) + _ ≤ _
  rw [pairSum_insert hx, mul_assoc]
  omega

private theorem enough_row_budget (k m : ℕ) (hk : 2 ≤ k) (hm : k + 3 ≤ m)
    (r : ℕ) (hr : r + ((k+6)/2 - 1) ≤ ((k+6)/2) * m) :
    4 * r ≤ m * (m + 2*k + 5) := by
  have h := Nat.le_of_add_right_le hr
  by_cases hm7 : 7 ≤ m
  · calc
      4 * r ≤ 4 * (((k+6)/2)*m) := Nat.mul_le_mul_left 4 h
      _ = m * (4*((k+6)/2)) := by ring
      _ ≤ m * (m + 2*k + 5) := Nat.mul_le_mul_left _ (by omega)
  · have hm' : m = 5 ∨ m = 6 := by omega
    have hk' : k = 2 ∨ k = 3 := by omega
    rcases hm' with rfl | rfl <;> rcases hk' with rfl | rfl <;> omega

private theorem sum_growth {G : SimpleGraph V} [DecidableEq V] (hc : G.Connected)
    {C : Finset V} (hc₃ : 3 ≤ C.card)
    (hcd : ∀ a ∈ C, ∀ b ∈ C, G.dist a b ≤ 4)
    (hbase : pairSum (square G) C + 4 * C.card ≤ 2*C.card*(C.card-1) + 6)
    (k : ℕ) (hk : 2 ≤ k) (hl : C.card + k ≤ Fintype.card V) :
    ∃ S : Finset V, C ⊆ S ∧ S.card = C.card + k ∧
      (∀ a ∈ S, ∀ b ∈ S, G.dist a b ≤ 4+k) ∧
      2 * pairSum (square G) S ≤ (k+2) * S.card * (S.card-1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have hC : C.Nonempty := card_pos.mp (by omega)
    obtain ⟨S₁, h₁, hn₁, hd₁, hsum₁⟩ :=
      step hc hC (by omega) (k := 0) (by simpa using hcd)
    obtain ⟨S₂, h₂, hn₂, hd₂, hsum₂⟩ :=
      step hc (hC.mono h₁) (by omega) (k := 1) hd₁
    refine ⟨S₂, h₁.trans h₂, by omega, hd₂, ?_⟩
    simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.reduceSub, Nat.mul_one] at hsum₁ hsum₂ ⊢
    rw [hn₂, hn₁]
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ C.card)
    have hsub' := Nat.sub_add_cancel (by omega : 1 ≤ C.card + 1 + 1)
    rw [hn₁] at hsum₂
    nlinarith
  | succ k hk ih =>
    obtain ⟨S, hS, hcard, hd, hsum⟩ := ih (by omega)
    have hnonempty : S.Nonempty := card_pos.mp (by omega)
    have hlt : S.card < Fintype.card V := by omega
    obtain ⟨x,hx,y,hy,hxy⟩ := choose_boundary_edge hc hnonempty hlt
    let U := insert x S
    have hu := insert_preserves_distance_bound hc hy hxy hd
    have huc : U.card = S.card+1 := card_insert_of_not_mem hx
    refine ⟨U, hS.trans (subset_insert _ _), by omega, hu, ?_⟩
    have hrow := row_bound hy (le_square G hxy) (r := (k+6)/2) (fun z hz => by
      have hp := hu x (mem_insert_self x _) z (mem_insert_of_mem hz)
      rw [square_dist hc]
      omega) (by omega)
    have hb := enough_row_budget k S.card hk (by omega) _ hrow
    have hidentity : (k+2)*S.card*(S.card-1)+S.card*(S.card+2*k+5) =
        (k+3)*(S.card+1)*S.card := by
      obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S.card ≠ 0)
      rw [ha, Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    calc
      2 * pairSum (square G) U = 2 * pairSum (square G) S +
          4 * ∑ z ∈ S, (square G).dist x z := by
        change 2 * pairSum (square G) (insert x S) = _
        rw [pairSum_insert hx]
        ring
      _ ≤ (k+2)*S.card*(S.card-1)+S.card*(S.card+2*k+5) := Nat.add_le_add hsum hb
      _ = (k+1+2)*U.card*(U.card-1) := by rw [huc, Nat.add_sub_cancel]; exact hidentity

omit [Fintype V] in
private theorem take_drop_lengths {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) (i : ℕ) :
    (p.take i).length = min i p.length ∧ (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.take, Walk.drop]
  | cons h p ih =>
    cases i with
    | zero => simp [Walk.take, Walk.drop]
    | succ i =>
      have h := ih i
      change (p.take i).length + 1 = min (i + 1) (p.length + 1) ∧
        (p.drop i).length = p.length + 1 - (i + 1)
      omega

omit [Fintype V] in
private theorem geodesic_prefix_suffix {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} {p : G.Walk v w} (hp : p.length = G.dist v w) {i : ℕ}
    (hi : i ≤ p.length) :
    G.dist v (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by
  have ht := G.dist_le (p.take i)
  have hd := G.dist_le (p.drop i)
  have hs := take_drop_lengths p i
  have htri : G.dist v w ≤ G.dist v (p.getVert i) + G.dist (p.getVert i) w :=
    hc.dist_triangle
  simp [min_eq_left hi] at hs
  omega


def twoBall (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter (fun w => G.dist v w ≤ 2)

private theorem mem_twoBall {G : SimpleGraph V} {v w : V} :
    w ∈ twoBall G v ↔ G.dist v w ≤ 2 := by simp [twoBall]

private theorem twoBall_diam {G : SimpleGraph V} (hc : G.Connected) (v : V) :
    ∀ a ∈ twoBall G v, ∀ b ∈ twoBall G v, G.dist a b ≤ 4 := by
  intro a ha b hb
  have h₁ := mem_twoBall.mp ha
  have h₂ := mem_twoBall.mp hb
  have ht := hc.dist_triangle (u := a) (v := v) (w := b)
  rw [G.dist_comm (u := a) (v := v)] at ht
  omega

omit [Fintype V] in
private theorem row_bound_with_two_neighbors {G : SimpleGraph V} [DecidableEq V]
    {S : Finset V} {x a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hxa : G.dist x a = 1) (hxb : G.dist x b = 1)
    (hd : ∀ z ∈ S, G.dist x z ≤ 2) :
    (∑ z ∈ S, G.dist x z) + 2 ≤ 2 * S.card := by
  have hb' : b ∈ S.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  have h₁ := sum_erase_add S (G.dist x) ha
  have h₂ := sum_erase_add (S.erase a) (G.dist x) hb'
  have h₃ : (∑ z ∈ (S.erase a).erase b, G.dist x z) ≤ 2 * ((S.erase a).erase b).card := by
    calc
      _ ≤ ∑ _ ∈ (S.erase a).erase b, 2 :=
        sum_le_sum (fun z hz => hd z (mem_of_mem_erase (mem_of_mem_erase hz)))
      _ = _ := by simp [Nat.mul_comm]
  have h₄ := card_erase_add_one ha
  have h₅ := card_erase_add_one hb'
  omega

omit [Fintype V] in
private theorem exists_near_neighbor_of_dist_two {G : SimpleGraph V} (hc : G.Connected)
    {v x : V} (hx : G.dist v x = 2) :
    ∃ a, G.dist v a = 1 ∧ G.Adj a x := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v x
  have hlen : p.length = 2 := hp.trans hx
  have hda := (geodesic_prefix_suffix hc hp (by omega : 1 ≤ p.length)).1
  have hab := p.adj_getVert_succ (i := 1) (by omega)
  have he : p.getVert (1+1) = x := p.getVert_of_length_le (by omega)
  rw [he] at hab
  exact ⟨p.getVert 1, hda, hab⟩

/-- Distances in the square restricted to a closed two-ball sum to at
most twice the number of ordered distinct pairs, with a deficit of
at least four times the ball size minus six. -/
theorem twoBall_pairSum {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected) (v : V) :
    pairSum (square G) (twoBall G v) + 4 * (twoBall G v).card ≤
      2*(twoBall G v).card*((twoBall G v).card - 1) + 6 := by
  classical
  let C := twoBall G v
  let K := univ.filter (fun w => G.dist v w ≤ 1)
  have hK (a : V) : a ∈ K ↔ G.dist v a ≤ 1 := by simp [K]
  have hvK : v ∈ K := (hK v).mpr (by simp [dist_self])
  have hKC : K ⊆ C := fun a ha => mem_twoBall.mpr ((hK a).mp ha |>.trans (by decide))
  have hK₂ : 2 ≤ K.card := by
    obtain ⟨x, hx⟩ := exists_ne v
    obtain ⟨p⟩ := hc.preconnected v x
    have ha := p.adj_snd (Walk.not_nil_of_ne hx.symm)
    have h1 : G.dist v p.snd = 1 := dist_eq_one_iff_adj.mpr ha
    have hsub : ({v,p.snd} : Finset V) ⊆ K := by
      intro a ha'
      rcases mem_insert.mp ha' with rfl | h
      · exact hvK
      · rw [mem_singleton.mp h]
        exact (hK _).mpr h1.le
    have hb := card_le_card hsub
    have hne : v ≠ p.snd := ha.ne
    rw [card_insert_of_not_mem (by simp [hne]), card_singleton] at hb
    exact hb
  have hcomplete {a b : V} (ha : a ∈ K) (hb : b ∈ K) (hne : a ≠ b) :
      (square G).dist a b = 1 := by
    apply dist_eq_one_iff_adj.mpr
    have h₁ := (hK a).mp ha
    have h₂ := (hK b).mp hb
    have ht := hc.dist_triangle (u := a) (v := v) (w := b)
    rw [G.dist_comm (u := a) (v := v)] at ht
    exact ⟨hne, by omega⟩
  have hsumK : pairSum (square G) K = K.card*(K.card-1) := by
    have hrow (a : V) (ha : a ∈ K) : (∑ b ∈ K, (square G).dist a b) = K.card-1 := by
      rw [← sum_erase_add K ((square G).dist a) ha, dist_self, add_zero]
      have he : (∑ b ∈ K.erase a, (square G).dist a b) = ∑ _b ∈ K.erase a, 1 := by
        exact sum_congr rfl (fun b hb =>
          hcomplete ha (mem_of_mem_erase hb) (mem_erase.mp hb).1.symm)
      rw [he]
      simp [card_erase_of_mem ha]
    unfold pairSum
    rw [sum_congr rfl hrow]
    simp
  have hbaseK : pairSum (square G) K + 4*K.card ≤ 2*K.card*(K.card-1)+6 := by
    rw [hsumK]
    have hsub := Nat.sub_add_cancel (by omega : 1 ≤ K.card)
    by_cases hh : 3 ≤ K.card
    · let t := K.card - 3
      have ht : K.card = t + 3 := by dsimp [t]; omega
      rw [ht, show t+3-1=t+2 by omega]
      nlinarith
    · have h : K.card = 2 := by omega
      simp [h]
  let candidates := C.powerset.filter (fun S => K ⊆ S ∧
    pairSum (square G) S + 4*S.card ≤ 2*S.card*(S.card-1)+6)
  have hKcandidate : K ∈ candidates :=
    mem_filter.mpr ⟨mem_powerset.mpr hKC, Subset.rfl, hbaseK⟩
  obtain ⟨S,hS,hmax⟩ :=
    exists_mem_eq_sup candidates ⟨K,hKcandidate⟩ Finset.card
  obtain ⟨hSC,hKS,hbaseS⟩ := mem_filter.mp hS
  have hsub : S ⊆ C := mem_powerset.mp hSC
  have heq : S = C := by
    by_cases he : S = C
    · exact he
    exfalso
    have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,he⟩)
    obtain ⟨x,hxC,hxS⟩ := exists_mem_not_mem_of_card_lt_card hlt
    have hxK : x ∉ K := fun h => hxS (hKS h)
    have hdx : G.dist v x = 2 := by
      have h₁ := mem_twoBall.mp hxC
      have h₂ : ¬G.dist v x ≤ 1 := fun h => hxK ((hK x).mpr h)
      omega
    obtain ⟨a,ha,hax⟩ := exists_near_neighbor_of_dist_two hc hdx
    have hxa : (square G).dist x a = 1 :=
      dist_eq_one_iff_adj.mpr (le_square G hax.symm)
    have hxv : (square G).dist x v = 1 := by
      rw [square_dist hc, G.dist_comm, hdx]
    have hne : v ≠ a := by intro h; rw [← h, dist_self] at ha; omega
    have hrow := row_bound_with_two_neighbors (hKS hvK) (hKS ((hK a).mpr ha.le))
      hne hxv hxa (fun z hz => by
        have := twoBall_diam hc v x hxC z (hsub hz)
        rw [square_dist hc]
        omega)
    have hnew : insert x S ∈ candidates := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hxC hsub), ?_⟩
      refine ⟨hKS.trans (subset_insert _ _), ?_⟩
      rw [pairSum_insert hxS, card_insert_of_not_mem hxS, Nat.add_sub_cancel]
      have h₁ : 1 ≤ S.card := card_pos.mpr ⟨v, hKS hvK⟩
      have h₂ := Nat.sub_add_cancel h₁
      nlinarith
    have hsle := le_sup (f := Finset.card) hnew
    rw [hmax, card_insert_of_not_mem hxS] at hsle
    omega
  change pairSum (square G) C + 4*C.card ≤ 2*C.card*(C.card-1)+6
  simpa only [heq] using hbaseS

private theorem twoBall_card_of_max_degree {G : SimpleGraph V} (hc : G.Connected) :
    ∃ v, (twoBall G v).card = squareMaxDegree G + 1 := by
  classical
  letI := hc.nonempty
  obtain ⟨v, hv⟩ := (square G).exists_maximal_degree_vertex
  have hset : twoBall G v = insert v (squareNeighbors G v) := by
    ext w
    rw [mem_twoBall, mem_insert]
    have hmem : w ∈ squareNeighbors G v ↔ v ≠ w ∧ G.dist v w ≤ 2 :=
      (square G).mem_neighborFinset v w
    rw [hmem]
    by_cases h : w = v
    · simp [h, dist_self]
    · simp [h, Ne.symm h]
  have hself : v ∉ squareNeighbors G v := by simp [squareNeighbors]
  refine ⟨v, ?_⟩
  rw [hset, card_insert_of_not_mem hself]
  change (square G).degree v + 1 = _
  exact congrArg (· + 1) hv.symm

private theorem twoBall_card_ge_three {G : SimpleGraph V} (hc : G.Connected) {v : V}
    (hcard : (twoBall G v).card < Fintype.card V) : 3 ≤ (twoBall G v).card := by
  classical
  obtain ⟨w, _, hw⟩ :=
    exists_mem_not_mem_of_card_lt_card (by rwa [card_univ] : (twoBall G v).card < (univ : Finset V).card)
  have hw' : 2 < G.dist v w := by
    apply Nat.lt_of_not_ge
    exact fun h => hw (mem_twoBall.mpr h)
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  let f : Fin 3 → (twoBall G v) := fun i =>
    ⟨p.getVert i.val, mem_twoBall.mpr (by
      have h := (geodesic_prefix_suffix hc hp (by omega : i.val ≤ p.length)).1
      omega)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Subtype.val h
    change p.getVert a.val = p.getVert b.val at hv
    have ha := (geodesic_prefix_suffix hc hp (by omega : a.val ≤ p.length)).1
    have hb := (geodesic_prefix_suffix hc hp (by omega : b.val ≤ p.length)).1
    rw [hv,hb] at ha
    exact ha.symm
  simpa using Fintype.card_le_of_injective f hf

/-- Once two or more vertices lie outside the largest closed two-ball,
the metric right side is bounded by n+1. -/
theorem metric_le_order_add_one_of_deficit_ge_two {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) (hdeficit : squareMaxDegree G + 3 ≤ Fintype.card V) :
    (squareMaxDegree G : ℚ) + 2 * averageDistance (square G) ≤ (Fintype.card V : ℚ) + 1 := by
  classical
  obtain ⟨v,hv⟩ := twoBall_card_of_max_degree hc
  let f := Fintype.card V - (twoBall G v).card
  have hfn : (twoBall G v).card + f = Fintype.card V := by omega
  have h₂ : 2 ≤ f := by omega
  have h3 := twoBall_card_ge_three hc (v := v) (by omega)
  obtain ⟨S, _, hs, _, hsum⟩ := sum_growth hc h3 (twoBall_diam hc v)
    (twoBall_pairSum hc v) f h₂ hfn.le
  have heq : S = univ := eq_univ_of_card S (hs.trans hfn)
  have hbound : 2 * pairSum (square G) univ ≤ (f+2) * (distinctPairs V).card := by
    rw [distinctPairs_card]
    simpa only [heq, card_univ, mul_assoc] using hsum
  have hdpos : (0 : ℚ) < ((distinctPairs V).card : ℚ) := by
    have hn : 1 < Fintype.card V := Fintype.one_lt_card
    have hpos : 0 < (distinctPairs V).card := by
      rw [distinctPairs_card]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hpos
  have hav : 2 * averageDistance (square G) ≤ (f : ℚ) + 2 := by
    unfold averageDistance
    rw [← mul_div_assoc, div_le_iff₀ hdpos]
    exact_mod_cast hbound
  have hcount : squareMaxDegree G + f + 2 = Fintype.card V + 1 := by omega
  have hcount' : (squareMaxDegree G : ℚ) + f + 2 = (Fintype.card V : ℚ) + 1 := by
    exact_mod_cast hcount
  linarith

/-- If the largest closed two-ball misses exactly one vertex, the
metric right side is strictly less than n+2. -/
theorem metric_lt_order_add_two_of_single_non_neighbor {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) (hdeficit : squareMaxDegree G + 2 = Fintype.card V) :
    (squareMaxDegree G : ℚ) + 2 * averageDistance (square G) < (Fintype.card V : ℚ) + 2 := by
  classical
  obtain ⟨v,hv⟩ := twoBall_card_of_max_degree hc
  let C := twoBall G v
  change C.card = squareMaxDegree G + 1 at hv
  have hC : C.Nonempty := ⟨v, mem_twoBall.mpr (by simp [dist_self])⟩
  have hcard : C.card + 1 = Fintype.card V := by omega
  have h3 : 3 ≤ C.card := twoBall_card_ge_three hc (v := v) (by change C.card < _; omega)
  obtain ⟨S, _, hs, _, hsum⟩ := step hc hC (by omega) (k := 0)
    (by simpa using twoBall_diam hc v)
  have heq : S = univ := eq_univ_of_card S (hs.trans hcard)
  have hbase : pairSum (square G) C + 4*C.card ≤ 2*C.card*(C.card-1)+6 :=
    twoBall_pairSum hc v
  have hsub := Nat.sub_add_cancel (by omega : 1 ≤ C.card)
  have hsum' : pairSum (square G) univ + 4 ≤ pairSum (square G) C + 6*C.card := by
    simpa [heq] using hsum
  have hbound : pairSum (square G) univ < 2 * (distinctPairs V).card := by
    rw [distinctPairs_card, ← hcard, Nat.add_sub_cancel]
    nlinarith
  have hpos : (0 : ℚ) < ((distinctPairs V).card : ℚ) := by
    have hn : 1 < Fintype.card V := Fintype.one_lt_card
    have hd : 0 < (distinctPairs V).card := by
      rw [distinctPairs_card]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hd
  have hav : averageDistance (square G) < 2 := by
    unfold averageDistance
    rw [div_lt_iff₀ hpos]
    exact_mod_cast hbound
  have hd : (squareMaxDegree G : ℚ) + 2 = (Fintype.card V : ℚ) := by
    exact_mod_cast hdeficit
  linarith

/-- The metric bound for a square with a universal vertex. -/
theorem metric_lt_order_add_three_of_universal {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) (hdeficit : squareMaxDegree G + 1 = Fintype.card V) :
    (squareMaxDegree G : ℚ) + 2 * averageDistance (square G) < (Fintype.card V : ℚ) + 3 := by
  obtain ⟨v,hv⟩ := twoBall_card_of_max_degree hc
  have hball : twoBall G v = univ := eq_univ_of_card _ (hv.trans hdeficit)
  have hb := twoBall_pairSum hc v
  rw [hball, card_univ] at hb
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  have hbound : pairSum (square G) univ < 2 * (distinctPairs V).card := by
    rw [distinctPairs_card, ← mul_assoc]
    omega
  have hpos : (0 : ℚ) < ((distinctPairs V).card : ℚ) := by
    simp only [distinctPairs_card]
    exact_mod_cast (Nat.mul_pos (by omega : 0 < Fintype.card V)
      (by omega : 0 < Fintype.card V-1))
  have hav : averageDistance (square G) < 2 := by
    unfold averageDistance
    rw [div_lt_iff₀ hpos]
    exact_mod_cast hbound
  have hd : (squareMaxDegree G : ℚ) + 1 = (Fintype.card V : ℚ) := by
    exact_mod_cast hdeficit
  linarith

private theorem extend_forest {G F : SimpleGraph V} (hc : G.Connected)
    (hFG : F ≤ G) (hf : F.IsAcyclic) : ∃ T, F ≤ T ∧ T ≤ G ∧ T.IsTree := by
  classical
  obtain ⟨T, hTG, hm⟩ := {H : SimpleGraph V | H.Connected ∧ F ≤ H}.toFinite.exists_minimal_le
    (show G.Connected ∧ F ≤ G from ⟨hc, hFG⟩)
  refine ⟨T, hm.prop.2, hTG, ⟨hm.prop.1, ?_⟩⟩
  intro v p hp
  by_cases hall : ∀ e ∈ p.edges, e ∈ F.edgeSet
  · exact hf (p.transfer F hall) (hp.transfer hall)
  push_neg at hall
  obtain ⟨e, hep, heF⟩ := hall
  induction e using Sym2.ind with
  | _ a b =>
    have heT := p.edges_subset_edgeSet hep
    have hbridge : ¬T.IsBridge s(a,b) :=
      fun h => (isBridge_iff_mem_and_forall_cycle_not_mem.mp h).2 p hp hep
    have hlt : T.deleteEdges {s(a,b)} < T := lt_of_le_of_ne (T.deleteEdges_le _) (by
      intro heq
      have hnot : ¬(T.deleteEdges {s(a,b)}).Adj a b := by simp
      rw [heq] at hnot
      exact hnot ((mem_edgeSet T).mp heT))
    apply hm.not_prop_of_lt hlt
    refine ⟨hm.prop.1.connected_delete_edge_of_not_isBridge hbridge, ?_⟩
    intro a' b' hab
    refine deleteEdges_adj.mpr ⟨hm.prop.2 hab, ?_⟩
    intro hEq
    exact heF ((Set.mem_singleton_iff.mp hEq) ▸ ((mem_edgeSet F).mpr hab))

def starAt (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ (a = v ∨ b = v)
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun a h => G.loopless a h.1

omit [Fintype V] in
private theorem starAt_acyclic (G : SimpleGraph V) (v : V) :
    (starAt G v).IsAcyclic := by
  classical
  intro a p hp
  have hout (w : V) (hw : w ∈ p.support) (hv : w ≠ v) : False := by
    let q := p.rotate hw
    have hq : q.IsCycle := hp.rotate hw
    have hs : q.snd = v := (q.adj_snd hq.not_nil).2.resolve_left hv
    have hpen : q.penultimate = v := (q.adj_penultimate hq.not_nil).2.resolve_right hv
    exact hq.snd_ne_penultimate (hs.trans hpen.symm)
  by_cases ha : a = v
  · have hAdj := p.adj_snd hp.not_nil
    exact hout p.snd (p.getVert_mem_support 1) (fun h => hAdj.ne (ha.trans h.symm))
  · exact hout a (by simpa only [Walk.getVert_zero] using p.getVert_mem_support 0) ha

private theorem maxLeaves_ge_tree_leaves {G T : SimpleGraph V} (hle : T ≤ G)
    (ht : T.IsTree) :
    letI : DecidableRel T.Adj := Classical.decRel _
    (univ.filter (fun v => T.degree v = 1)).card ≤ maxLeaves G := by
  classical
  apply le_csSup
  · refine ⟨Fintype.card V, ?_⟩
    rintro _ ⟨S, _, _, rfl⟩
    exact card_le_univ _
  · exact ⟨T, hle, ht, rfl⟩

private theorem tree_leaf_bounds {T : SimpleGraph V} [Nontrivial V] (ht : T.IsTree) :
    letI : DecidableRel T.Adj := Classical.decRel _
    2 ≤ (univ.filter (fun v => T.degree v = 1)).card ∧
      ∀ v, T.degree v ≤ (univ.filter (fun v => T.degree v = 1)).card := by
  classical
  let L := univ.filter (fun v => T.degree v = 1)
  let d (v : V) := T.degree v + if v ∈ L then 1 else 0
  have hpoint (v : V) : 2 ≤ d v := by
    have hpos : 0 < T.degree v := by
      obtain ⟨w, hw⟩ := exists_ne v
      obtain ⟨p⟩ := ht.isConnected.preconnected v w
      exact (T.degree_pos_iff_exists_adj v).mpr ⟨_, p.adj_snd (Walk.not_nil_of_ne hw.symm)⟩
    by_cases hd : T.degree v = 1
    · simp [d, L, hd]
    · simp [d, L, hd]
      omega
  have hsum : (∑ v, d v) + 2 = 2*Fintype.card V + L.card := by
    have he := ht.card_edgeFinset
    have hleaf : (∑ v : V, (if v ∈ L then 1 else 0 : ℕ)) = L.card := by simp
    unfold d
    rw [sum_add_distrib, T.sum_degrees_eq_twice_card_edges, hleaf]
    omega
  have hleft : (∑ _v : V, (2 : ℕ)) = 2 * Fintype.card V := by simp [Nat.mul_comm]
  change 2 ≤ L.card ∧ ∀ v, T.degree v ≤ L.card
  refine ⟨?_, ?_⟩
  · have he : (∑ _v : V, (2 : ℕ)) ≤ ∑ v, d v := sum_le_sum (fun v _ => hpoint v)
    rw [hleft] at he
    omega
  · intro v
    have hle : (∑ w : V, (2 + if w = v then T.degree v - 2 else 0)) ≤ ∑ w, d w := by
      apply sum_le_sum
      intro w _
      by_cases h : w = v
      · subst w
        rw [if_pos rfl]
        have hpv := hpoint v
        have hdeg : T.degree v ≤ d v := Nat.le_add_right _ _
        omega
      · simpa [h] using hpoint w
    rw [sum_add_distrib, hleft] at hle
    simp only [sum_ite_eq', mem_univ, if_true] at hle
    omega

private theorem two_le_maxLeaves {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected) :
    2 ≤ maxLeaves G := by
  classical
  obtain ⟨T, hTG, ht⟩ := hc.exists_isTree_le
  exact (tree_leaf_bounds ht).1.trans (maxLeaves_ge_tree_leaves hTG ht)

theorem degree_le_maxLeaves {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected)
    (v : V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.degree v ≤ maxLeaves G := by
  classical
  obtain ⟨T, hstar, hTG, ht⟩ := extend_forest hc
    (show starAt G v ≤ G from fun _ _ h => h.1) (starAt_acyclic G v)
  have hd : G.degree v ≤ T.degree v := by
    apply card_le_card
    intro w hw
    exact (T.mem_neighborFinset _ _).mpr (hstar ⟨(G.mem_neighborFinset _ _).mp hw, Or.inl rfl⟩)
  exact hd.trans (((tree_leaf_bounds ht).2 v).trans (maxLeaves_ge_tree_leaves hTG ht))

private theorem twoBall_card_le_five {G : SimpleGraph V} (hc : G.Connected)
    (hD : letI : DecidableRel G.Adj := Classical.decRel _
      ∀ v, G.degree v ≤ 2) (v : V) : (twoBall G v).card ≤ 5 := by
  classical
  let N := G.neighborFinset v
  let M := N.biUnion (fun a => (G.neighborFinset a).erase v)
  have hset : twoBall G v ⊆ insert v (N ∪ M) := by
    intro a ha
    by_cases hav : a = v
    · exact mem_insert.mpr (Or.inl hav)
    have hd := mem_twoBall.mp ha
    have hp := hc.pos_dist_of_ne (Ne.symm hav)
    by_cases hd₁ : G.dist v a = 1
    · exact mem_insert_of_mem (mem_union_left _ ((G.mem_neighborFinset _ _).mpr
        (dist_eq_one_iff_adj.mp hd₁)))
    · have hd₂ : G.dist v a = 2 := by omega
      obtain ⟨w, hw, hwa⟩ := exists_near_neighbor_of_dist_two hc hd₂
      apply mem_insert_of_mem
      apply mem_union_right
      exact mem_biUnion.mpr ⟨w, (G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp hw),
        mem_erase.mpr ⟨hav, (G.mem_neighborFinset _ _).mpr hwa⟩⟩
  have hn : N.card ≤ 2 := hD v
  have hm : M.card ≤ 2 := by
    calc
      _ ≤ ∑ a ∈ N, ((G.neighborFinset a).erase v).card := card_biUnion_le
      _ ≤ ∑ _a ∈ N, 1 := sum_le_sum (fun a ha => by
        have hmem := (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ha).symm
        have h := card_erase_add_one hmem
        have ht := hD a
        rw [G.card_neighborFinset_eq_degree] at h
        omega)
      _ ≤ 2 := by simpa using hn
  have hb := card_le_card hset
  have h₂ := card_insert_le v (N ∪ M)
  have h₃ := card_union_le N M
  omega

private theorem order_five_metric_le_order_add_two {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) (hn : Fintype.card V ≤ 5)
    (hq : squareMaxDegree G + 1 = Fintype.card V) :
    (squareMaxDegree G : ℚ) + 2 * averageDistance (square G) ≤ (Fintype.card V : ℚ) + 2 := by
  obtain ⟨v, hv⟩ := twoBall_card_of_max_degree hc
  have hball : twoBall G v = univ := eq_univ_of_card _ (hv.trans hq)
  have hB := twoBall_pairSum hc v
  rw [hball, card_univ] at hB
  have hn₂ : 1 < Fintype.card V := Fintype.one_lt_card
  have hb : 2*pairSum (square G) univ ≤ 3*(distinctPairs V).card := by
    rw [distinctPairs_card]
    have hcases : Fintype.card V = 2 ∨ Fintype.card V = 3 ∨
        Fintype.card V = 4 ∨ Fintype.card V = 5 := by omega
    rcases hcases with ha | ha | ha | ha <;> rw [ha] at hB ⊢ <;> omega
  have hp : (0 : ℚ) < ((distinctPairs V).card : ℚ) := by
    simp only [distinctPairs_card]
    exact_mod_cast (Nat.mul_pos (by omega : 0 < Fintype.card V)
      (by omega : 0 < Fintype.card V-1))
  have hM : 2*averageDistance (square G) ≤ 3 := by
    unfold averageDistance
    rw [← mul_div_assoc, div_le_iff₀ hp]
    exact_mod_cast hb
  have hq' : (squareMaxDegree G : ℚ) + 1 = (Fintype.card V : ℚ) := by exact_mod_cast hq
  linarith

theorem conjecture185_bipartite {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected)
    (hbi : ∃ c : V → Bool, ∀ a b, G.Adj a b → c a ≠ c b) : Claim185 G := by
  classical
  obtain ⟨c, hc'⟩ := hbi
  have hu : (univ : Finset V) ∈ univ.powerset.filter (fun s : Finset V =>
      ∃ k : s → Bool, ∀ a b : s, G.Adj a.val b.val → k a ≠ k b) :=
    mem_filter.mpr ⟨mem_powerset.mpr (Subset.rfl), ⟨fun v => c v.val,
      fun a b h => hc' a.val b.val h⟩⟩
  have hb : Fintype.card V ≤ bipartiteNumber G := by
    have ht := le_sup (f := Finset.card) hu
    simpa only [bipartiteNumber, card_univ] using ht
  have ht := two_le_maxLeaves hc
  have hb' : (Fintype.card V : ℚ) ≤ (bipartiteNumber G : ℚ) := by exact_mod_cast hb
  have ht' : 2 ≤ (maxLeaves G : ℚ) := by exact_mod_cast ht
  have hq : squareMaxDegree G < Fintype.card V := (square G).maxDegree_lt_card_verts
  unfold Claim185
  by_cases h1 : squareMaxDegree G + 1 = Fintype.card V
  · by_cases hD : ∀ v, G.degree v ≤ 2
    · obtain ⟨v, hv⟩ := twoBall_card_of_max_degree hc
      have h5 := twoBall_card_le_five hc hD v
      have hmet := order_five_metric_le_order_add_two hc (by omega) h1
      linarith
    · obtain ⟨v, hv⟩ := not_forall.mp hD
      have hl : 3 ≤ maxLeaves G := (Nat.lt_of_not_ge hv).trans_le (degree_le_maxLeaves hc v)
      have hl' : 3 ≤ (maxLeaves G : ℚ) := by exact_mod_cast hl
      have hmet := metric_lt_order_add_three_of_universal hc h1
      linarith
  · by_cases h2 : squareMaxDegree G + 2 = Fintype.card V
    · have hmet := metric_lt_order_add_two_of_single_non_neighbor hc h2
      linarith
    · have hmet := metric_le_order_add_one_of_deficit_ge_two hc (by omega)
      linarith

/-- The ordered nonedges of a graph. -/
def nonadjacentPairs (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact (distinctPairs V).filter (fun p => ¬ G.Adj p.1 p.2)

/-- When distances are at most two, their excess over one is exactly the nonedge fraction. -/
theorem averageDistance_eq_one_add_nonedge_fraction {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) (hdiam : ∀ x y, G.dist x y ≤ 2) :
    averageDistance G = 1 + ((nonadjacentPairs G).card : ℚ) / (distinctPairs V).card := by
  classical
  have hs : pairSum G univ = (distinctPairs V).card + (nonadjacentPairs G).card := by
    rw [pairSum_eq_distinct_sum]
    calc
      _ = ∑ p ∈ distinctPairs V, (1 + if ¬ G.Adj p.1 p.2 then 1 else 0) := by
        apply sum_congr rfl
        intro p hp
        have hne : p.1 ≠ p.2 := by
          simpa [distinctPairs, mem_offDiag] using hp
        by_cases ha : G.Adj p.1 p.2
        · simp [ha, dist_eq_one_iff_adj.mpr ha]
        · have hpos := hc.pos_dist_of_ne hne
          have hbound := hdiam p.1 p.2
          have hne₁ : G.dist p.1 p.2 ≠ 1 := fun h => ha (dist_eq_one_iff_adj.mp h)
          have he : G.dist p.1 p.2 = 2 := by omega
          simp [he, ha]
      _ = (distinctPairs V).card + (nonadjacentPairs G).card := by
        rw [sum_add_distrib]
        rw [sum_boole (fun p : V × V => ¬G.Adj p.1 p.2)]
        simp [nonadjacentPairs]
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  have hd : (0 : ℚ) < (distinctPairs V).card := by
    rw [distinctPairs_card]
    exact_mod_cast (Nat.mul_pos (by omega : 0 < Fintype.card V)
      (by omega : 0 < Fintype.card V - 1))
  rw [averageDistance, hs, Nat.cast_add, add_div, div_self hd.ne']

/-- The published order bound reduces failure of the conjecture to three explicit cases. -/
theorem counterexample_iff_of_order_bound {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) (horder : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNumber G) :
    ¬Claim185 G ↔
      (squareMaxDegree G + 1 = Fintype.card V ∧
        ((maxLeaves G + bipartiteNumber G = Fintype.card V + 1 ∧
            1 < averageDistance (square G)) ∨
          (maxLeaves G + bipartiteNumber G = Fintype.card V + 2 ∧
            (3 / 2 : ℚ) < averageDistance (square G)))) ∨
      (squareMaxDegree G + 2 = Fintype.card V ∧
        maxLeaves G + bipartiteNumber G = Fintype.card V + 1 ∧
        (3 / 2 : ℚ) < averageDistance (square G)) := by
  classical
  have hq : squareMaxDegree G < Fintype.card V := (square G).maxDegree_lt_card_verts
  unfold Claim185
  rw [not_le, ← Nat.cast_add]
  constructor
  · intro h
    by_cases h₀ : squareMaxDegree G + 1 = Fintype.card V
    · left
      refine ⟨h₀, ?_⟩
      have hq' : (squareMaxDegree G : ℚ) + 1 = (Fintype.card V : ℚ) := by
        exact_mod_cast h₀
      have hmetric := metric_lt_order_add_three_of_universal hc h₀
      have hs' : ((maxLeaves G + bipartiteNumber G : ℕ) : ℚ) <
          (Fintype.card V : ℚ) + 3 := h.trans hmetric
      have hs : maxLeaves G + bipartiteNumber G < Fintype.card V + 3 := by
        exact_mod_cast hs'
      have heq : maxLeaves G + bipartiteNumber G = Fintype.card V + 1 ∨
          maxLeaves G + bipartiteNumber G = Fintype.card V + 2 := by omega
      rcases heq with h₁ | h₂
      · exact Or.inl ⟨h₁, by rw [h₁, Nat.cast_add, Nat.cast_one] at h; linarith⟩
      · exact Or.inr ⟨h₂, by rw [h₂, Nat.cast_add, Nat.cast_ofNat] at h; linarith⟩
    · by_cases h₁ : squareMaxDegree G + 2 = Fintype.card V
      · right
        have hq' : (squareMaxDegree G : ℚ) + 2 = (Fintype.card V : ℚ) := by
          exact_mod_cast h₁
        have hmetric := metric_lt_order_add_two_of_single_non_neighbor hc h₁
        have hs' : ((maxLeaves G + bipartiteNumber G : ℕ) : ℚ) <
            (Fintype.card V : ℚ) + 2 := h.trans hmetric
        have hs : maxLeaves G + bipartiteNumber G < Fintype.card V + 2 := by
          exact_mod_cast hs'
        have hs₁ : maxLeaves G + bipartiteNumber G = Fintype.card V + 1 := by omega
        refine ⟨h₁, hs₁, ?_⟩
        rw [hs₁, Nat.cast_add, Nat.cast_one] at h
        linarith
      · have hmetric := metric_le_order_add_one_of_deficit_ge_two hc (by omega)
        have horder' : (Fintype.card V : ℚ) + 1 ≤
            ((maxLeaves G + bipartiteNumber G : ℕ) : ℚ) := by exact_mod_cast horder
        exact (not_lt_of_ge (hmetric.trans horder') h).elim
  · rintro (⟨hq, ⟨hs, ha⟩ | ⟨hs, ha⟩⟩ | ⟨hq, hs, ha⟩)
    · have hq' : (squareMaxDegree G : ℚ) + 1 = (Fintype.card V : ℚ) := by
        exact_mod_cast hq
      rw [hs, Nat.cast_add, Nat.cast_one]
      linarith
    · have hq' : (squareMaxDegree G : ℚ) + 1 = (Fintype.card V : ℚ) := by
        exact_mod_cast hq
      rw [hs, Nat.cast_add, Nat.cast_ofNat]
      linarith
    · have hq' : (squareMaxDegree G : ℚ) + 2 = (Fintype.card V : ℚ) := by
        exact_mod_cast hq
      rw [hs, Nat.cast_add, Nat.cast_one]
      linarith

#print axioms claim185_cross_multiply
#print axioms twoBall_pairSum
#print axioms metric_le_order_add_one_of_deficit_ge_two
#print axioms metric_lt_order_add_two_of_single_non_neighbor
#print axioms metric_lt_order_add_three_of_universal
#print axioms conjecture185_bipartite
#print axioms averageDistance_eq_one_add_nonedge_fraction
#print axioms counterexample_iff_of_order_bound

end
end Graffiti185
