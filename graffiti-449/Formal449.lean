import Std
set_option warningAsError true

namespace Graffiti449

def sumMap {V : Type} (l : List V) (f : V → Nat) : Nat :=
  (l.map f).sum

theorem sumMapMono {V : Type} (l : List V) (f g : V → Nat)
    (h : ∀ u ∈ l, f u ≤ g u) : sumMap l f ≤ sumMap l g := by
  induction l with
  | nil => simp [sumMap]
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun u hu => h u (by simp [hu]))
    simp only [sumMap, List.map_cons, List.sum_cons] at *
    omega

theorem sumMapAdd {V : Type} (l : List V) (f g : V → Nat) :
    sumMap l (fun u => f u+g u) = sumMap l f + sumMap l g := by
  induction l with
  | nil => simp [sumMap]
  | cons a l ih =>
    simp only [sumMap, List.map_cons, List.sum_cons] at *
    omega

theorem sumMapDouble {V : Type} (l : List V) (f : V → Nat) :
    sumMap l (fun u => 2*f u) = 2*sumMap l f := by
  have h := sumMapAdd l f f
  simpa only [Nat.two_mul] using h

theorem sumMapSwap {V : Type} (l m : List V) (f : V → V → Nat) :
    sumMap l (fun x => sumMap m (f x)) =
    sumMap m (fun y => sumMap l (fun x => f x y)) := by
  induction l with
  | nil =>
    have h : sumMap m (fun _ => 0) = 0 := by
      induction m with
      | nil => rfl
      | cons a m ih => simpa [sumMap] using ih
    simpa [sumMap] using h.symm
  | cons x l ih =>
    change sumMap m (f x) + sumMap l (fun x => sumMap m (f x)) = _
    rw [ih, ← sumMapAdd]
    rfl

abbrev Graph (n : Nat) := Fin n → Fin n → Bool
abbrev Subset (n : Nat) := Fin n → Bool

def verts (n : Nat) : List (Fin n) := List.ofFn id
def bit (b : Bool) : Nat := if b then 1 else 0

def card {n} (I : Subset n) : Nat := sumMap (verts n) (fun u => bit (I u))
def degree {n} (G : Graph n) (u : Fin n) : Nat := card (G u)
def high {n} (G : Graph n) : Subset n := fun u => decide (3 ≤ degree G u)
def low {n} (G : Graph n) : Subset n := fun u => !high G u

def pairCount {n} (G : Graph n) (P Q : Subset n) : Nat :=
  sumMap (verts n) (fun u => sumMap (verts n) (fun v => bit (P u && Q v && G u v)))

def localCount {n} (G : Graph n) (I : Subset n) (u : Fin n) : Nat :=
  card (fun v => I v && G u v)

theorem cardSplit {n} (P Q : Subset n) :
    card P = card (fun u => P u && Q u) + card (fun u => P u && !Q u) := by
  unfold card
  rw [← sumMapAdd]
  unfold sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  cases hp : P u <;> cases hq : Q u <;> simp [hp, hq, bit]

theorem pairSwap {n} (G : Graph n) (hs : ∀ u v, G u v = G v u) (P Q : Subset n) :
    pairCount G P Q = pairCount G Q P := by
  unfold pairCount
  rw [sumMapSwap]
  unfold sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  congr 1
  apply List.map_congr_left
  intro v _
  rw [hs v u, Bool.and_comm (P v) (Q u)]

theorem pairSplit {n} (G : Graph n) (P Q R : Subset n) :
    pairCount G P Q = pairCount G P (fun u => Q u && R u) + pairCount G P (fun u => Q u && !R u) := by
  unfold pairCount
  rw [← sumMapAdd]
  unfold sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  have h := sumMapAdd (verts n)
    (fun v => bit (P u && (Q v && R v) && G u v))
    (fun v => bit (P u && (Q v && !R v) && G u v))
  unfold sumMap at h
  rw [← h]
  congr 1
  apply List.map_congr_left
  intro v _
  cases P u <;> cases Q v <;> cases R v <;> cases G u v <;> rfl

theorem pairMono {n} (G : Graph n) (P Q P' Q' : Subset n)
    (hp : ∀ u, P u = true → P' u = true) (hq : ∀ u, Q u = true → Q' u = true) :
    pairCount G P Q ≤ pairCount G P' Q' := by
  unfold pairCount
  apply sumMapMono
  intro u _
  apply sumMapMono
  intro v _
  cases he : P u && Q v && G u v with
  | false => exact Nat.zero_le _
  | true =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at he
    simp [hp u he.1.1, hq v he.1.2, he.2, bit]

theorem pairRows {n} (G : Graph n) (P Q : Subset n) :
    pairCount G P Q = sumMap (verts n) (fun u => if P u then localCount G Q u else 0) := by
  unfold pairCount sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  cases hu : P u
  · simp only [hu, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bit]
    induction (verts n) with
    | nil => rfl
    | cons a l ih => simp [ih]
  · simp [hu, localCount, card, sumMap]

theorem degreeSplit {n} (G : Graph n) (I : Subset n) (u : Fin n) :
    degree G u = localCount G I u + localCount G (fun u => !I u) u := by
  have h := cardSplit (G u) I
  simpa [degree, localCount, Bool.and_comm] using h

def TwoIndependent {n} (G : Graph n) (I : Subset n) : Prop :=
  ∀ u, I u = true → localCount G I u ≤ 1

/-- In a symmetric loopless graph, each induced edge has exactly the two
orientations counted by pairCount; division by two gives its cardinality. -/
def inducedEdges {n} (G : Graph n) (I : Subset n) : Nat :=
  pairCount G I I / 2

theorem conjecture449_bound {n} (G : Graph n) (hs : ∀ u v, G u v = G v u)
    (I : Subset n) (hi : TwoIndependent G I) :
    card I ≤ card (low G) + inducedEdges G (high G) / 2 := by
  let H := high G
  let L := low G
  let A : Subset n := fun u => H u && I u
  let B : Subset n := fun u => L u && !I u
  let C : Subset n := fun u => H u && !I u
  let U : Subset n := fun u => !I u
  have hlo : ∀ u, L u = !H u := fun _ => rfl
  have hHi (u : Fin n) (h : A u = true) : 3 ≤ degree G u := by
    have hH : H u = true := (Bool.and_eq_true _ _).mp h |>.1
    simpa [H, high] using hH
  have hl (u : Fin n) (h : B u = true) : degree G u ≤ 2 := by
    have hL : L u = true := (Bool.and_eq_true _ _).mp h |>.1
    have hlt : ¬ 3 ≤ degree G u := by simpa [L, low, high] using hL
    omega
  have first : 2*card A ≤ pairCount G A U := by
    unfold card
    rw [← sumMapDouble, pairRows]
    apply sumMapMono
    intro u _
    cases h : A u
    · simp [h, bit]
    · have hu : I u = true := (Bool.and_eq_true _ _).mp h |>.2
      have hdeg := hHi u h
      have hsel := hi u hu
      have hd := degreeSplit G I u
      change degree G u = localCount G I u + localCount G U u at hd
      simp [h, bit]
      omega
  have second : pairCount G A B ≤ 2*card B := by
    rw [pairSwap G hs A B]
    unfold card
    rw [← sumMapDouble, pairRows]
    apply sumMapMono
    intro u _
    cases h : B u
    · simp [h, bit]
    · have hd := hl u h
      have hm : localCount G A u ≤ degree G u := by
        unfold localCount degree card
        apply sumMapMono
        intro v _
        cases hv : A v <;> cases hg : G u v <;> simp [hv, hg, bit]
      simp [h, bit]
      omega
  have hparts : pairCount G A U = pairCount G A C + pairCount G A B := by
    have h := pairSplit G A U H
    simpa [C, B, L, low, U, H, Bool.and_comm] using h
  have htwice : 2*pairCount G A C ≤ pairCount G H H := by
    have h := pairSplit G H H I
    change pairCount G H H = pairCount G H A + pairCount G H C at h
    have hA : ∀ u, A u = true → H u = true :=
      fun u hu => (Bool.and_eq_true _ _).mp hu |>.1
    have hC : ∀ u, C u = true → H u = true :=
      fun u hu => (Bool.and_eq_true _ _).mp hu |>.1
    have h1 := pairMono G C A H A hC (fun _ h => h)
    have h2 := pairMono G A C H C hA (fun _ h => h)
    rw [pairSwap G hs C A] at h1
    omega
  have hcross : pairCount G A C ≤ inducedEdges G H := by
    unfold inducedEdges
    omega
  have hselec := cardSplit I H
  have hlow := cardSplit L I
  have hA : card (fun u => I u && H u) = card A := by simp [A, Bool.and_comm]
  have hB : card (fun u => L u && !I u) = card B := rfl
  have hC : card (fun u => I u && !H u) = card (fun u => L u && I u) := by
    simp [L, low, H, Bool.and_comm]
  rw [hA,hC] at hselec
  rw [hB] at hlow
  change card I ≤ card L + inducedEdges G H / 2
  omega


def Attainable {n} (G : Graph n) (k : Nat) : Prop :=
  ∃ I, TwoIndependent G I ∧ card I = k

theorem attainedEmpty {n} (G : Graph n) : Attainable G 0 := by
  refine ⟨fun _ => false, fun _ h => Bool.noConfusion h, ?_⟩
  unfold card
  induction (verts n) with
  | nil => rfl
  | cons a l ih => simp [sumMap, bit] at *; exact ih

theorem cardLeOrder {n} (I : Subset n) : card I ≤ n := by
  have h : sumMap (verts n) (fun _ => 1) = n := by
    have hl : ∀ l : List (Fin n), sumMap l (fun _ => 1) = l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [sumMap, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
    simpa [verts] using hl (verts n)
  calc
    card I ≤ sumMap (verts n) (fun _ => 1) := sumMapMono _ _ _ (fun u _ => by cases I u <;> decide)
    _ = n := h

theorem maxNatExists (P : Nat → Prop) (bound : Nat)
    (h0 : P 0) (hb : ∀ k, P k → k ≤ bound) :
    ∃ k, P k ∧ ∀ j, P j → j ≤ k := by
  classical
  induction bound with
  | zero => exact ⟨0, h0, hb⟩
  | succ m ih =>
    by_cases h : P (m+1)
    · exact ⟨m+1,h,hb⟩
    · apply ih
      intro k hk
      have hkm := hb k hk
      have hneq : k ≠ m+1 := fun e => h (e ▸ hk)
      omega

/-- Exactly the maximum size of an induced subgraph of maximum degree one. -/
noncomputable def twoIndependenceNumber {n} (G : Graph n) : Nat :=
  Classical.choose <| maxNatExists (Attainable G) n (attainedEmpty G)
    (fun _ ⟨I, _, e⟩ => e ▸ cardLeOrder I)

/-- Catalogue #449; floor(m/2) equals ceiling((m−1)/2) for integral m≥0.
The no-loop condition is unnecessary for the stronger directed-count inequality. -/
theorem conjecture449 {n} (G : Graph n) (hs : ∀ u v, G u v = G v u) :
    twoIndependenceNumber G ≤ card (low G) + inducedEdges G (high G) / 2 := by
  obtain ⟨I, hI, hcard⟩ := (Classical.choose_spec (maxNatExists (Attainable G) n (attainedEmpty G)
    (fun _ ⟨I, _, e⟩ => e ▸ cardLeOrder I))).1
  change card I = twoIndependenceNumber G at hcard
  rw [← hcard]
  exact conjecture449_bound G hs I hI

#print axioms conjecture449
end Graffiti449
