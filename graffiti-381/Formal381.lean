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

namespace Graffiti381
open Graffiti449

def adjOfDegree {n} (G : Graph n) (d : Nat) : Subset n :=
  fun v => decide (degree G v = d)

def neighbor {n} (G : Graph n) (S : Subset n) : Subset n :=
  fun v => decide (0 < localCount G S v)

def support {n} (G : Graph n) : Subset n := neighbor G (adjOfDegree G 1)
def isolatedIn {n} (G : Graph n) (S : Subset n) : Subset n :=
  fun v => S v && !(neighbor G S v)

def maxDegreeIn {n} (G : Graph n) (S : Subset n) : Nat :=
  ((verts n).map fun v => if S v then degree G v else 0).foldr max 0

def TotalDom {n} (G : Graph n) (S : Subset n) : Prop :=
  ∀ u, 0 < localCount G S u

inductive Walk {n} (G : Graph n) : Fin n → Fin n → Prop
  | nil (v) : Walk G v v
  | step {u v w} : G u v = true → Walk G v w → Walk G u w

def Connected {n} (G : Graph n) : Prop := ∀ x y, Walk G x y

theorem cardPosList {V : Type} (l : List V) (P : V → Bool) :
    0 < sumMap l (fun u => bit (P u)) ↔ ∃ u ∈ l, P u = true := by
  induction l with
  | nil => simp [sumMap]
  | cons a l ih =>
    cases ha : P a
    · simp [sumMap, bit, ha, List.mem_cons] at *; exact ih
    · constructor
      · intro _
        exact ⟨a,by simp,ha⟩
      · intro _
        change 0 < bit (P a) + sumMap l (fun u => bit (P u))
        simp [bit,ha]; omega

theorem memVerts {n} (u : Fin n) : u ∈ verts n :=
  List.mem_ofFn.mpr ⟨u,rfl⟩

theorem neighbor_iff {n} (G : Graph n) (S : Subset n) (v : Fin n) :
    neighbor G S v = true ↔ ∃ u, S u = true ∧ G v u = true := by
  change decide (0 < localCount G S v) = true ↔ _
  rw [decide_eq_true_eq]
  unfold localCount card
  rw [cardPosList]
  constructor
  · rintro ⟨u,_,h⟩
    rw [Bool.and_eq_true] at h
    exact ⟨u,h⟩
  · rintro ⟨u,hu,hG⟩
    exact ⟨u,memVerts u,by simp [hu,hG]⟩

theorem local_pos_iff {n} (G : Graph n) (S : Subset n) (v : Fin n) :
    0 < localCount G S v ↔ ∃ u, S u = true ∧ G v u = true := by
  rw [← neighbor_iff]
  simp [neighbor]

theorem sumMapTwo {V : Type} [DecidableEq V] (l : List V) (P : V → Bool) {u v : V}
    (hu : u ∈ l) (hv : v ∈ l) (hp : P u = true) (hq : P v = true) (hne : u ≠ v) :
    2 ≤ sumMap l (fun u => bit (P u)) := by
  have haux : ∀ (l : List V) (a : V), a ∈ l → P a = true → 1 ≤ sumMap l (fun u => bit (P u)) := by
    intro l a ha hpa
    induction l with
    | nil => simp at ha
    | cons b l ih =>
      simp only [sumMap, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp ha with h | h
      · subst b
        simp [bit,hpa]
      · have h' := ih h
        unfold sumMap at h'
        omega
  induction l with
  | nil => simp at hu
  | cons a l ih =>
    simp only [sumMap, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hu with h1 | h1
    · subst a
      have hv' : v ∈ l := (List.mem_cons.mp hv).resolve_left (Ne.symm hne)
      have hh := haux l v hv' hq
      unfold sumMap at hh
      simp only [bit,hp,if_true] at *
      omega
    · rcases List.mem_cons.mp hv with h2 | h2
      · subst a
        have hh := haux l u h1 hp
        unfold sumMap at hh
        simp only [bit,hq,if_true] at *
        omega
      · have hh := ih h1 h2
        unfold sumMap at hh
        omega

theorem degreeOneUnique {n} (G : Graph n) {u x y : Fin n}
    (h : degree G u = 1) (hx : G u x = true) (hy : G u y = true) : x = y := by
  classical
  apply Classical.byContradiction
  intro hn
  have h2 := sumMapTwo (verts n) (G u) (memVerts x) (memVerts y) hx hy hn
  change 2 ≤ degree G u at h2
  omega

theorem noAdjacentLeaves {n} (G : Graph n) (hn : 2 < n) (hc : Connected G)
    (hs : ∀ x y, G x y = G y x) {x y : Fin n} (hxy : G x y = true)
    (hx : degree G x = 1) (hy : degree G y = 1) : False := by
  classical
  have closed : ∀ u v, u = x ∨ u = y → G u v = true → v = x ∨ v = y := by
    intro u v hu hv
    rcases hu with hh | hh <;> subst u
    · exact Or.inr (degreeOneUnique G hx hv hxy)
    · exact Or.inl (degreeOneUnique G hy hv ((hs x y).symm.trans hxy))
  have step : ∀ {u v}, Walk G u v → (u = x ∨ u = y) → v = x ∨ v = y := by
    intro u v hw
    induction hw with
    | nil _ => exact id
    | @step u z v ha hw ih => exact fun hu => ih (closed u z hu ha)
  have all := fun v => step (hc x v) (Or.inl rfl)
  have e0 := all (⟨0, by omega⟩ : Fin n)
  have e1 := all (⟨1, by omega⟩ : Fin n)
  have e2 := all (⟨2, by omega⟩ : Fin n)
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
    (try have e0' := congrArg Fin.val e0; try have e1' := congrArg Fin.val e1;
     try have e2' := congrArg Fin.val e2; simp at *; omega)

theorem supportForced {n} (G : Graph n) (hs : ∀ x y, G x y = G y x)
    {D : Subset n} (hd : TotalDom G D) {v : Fin n} (hv : support G v = true) : D v = true := by
  obtain ⟨l, hl, hvl⟩ := (neighbor_iff G (adjOfDegree G 1) v).mp hv
  have hdeg : degree G l = 1 := by simpa [adjOfDegree] using hl
  obtain ⟨u, hu, hlu⟩ := (local_pos_iff G D l).mp (hd l)
  have e := degreeOneUnique G hdeg hlu ((hs v l).symm.trans hvl)
  simpa [e] using hu

theorem supportDegree {n} (G : Graph n) (hn : 2 < n)
    (hc : Connected G) (hs : ∀ x y, G x y = G y x)
    {v} (hv : support G v = true) : 2 ≤ degree G v := by
  obtain ⟨l, hl, hvl⟩ := (neighbor_iff G (adjOfDegree G 1) v).mp hv
  have hdeg : degree G l = 1 := by simpa [adjOfDegree] using hl
  have hpos : 0 < degree G v :=
    (cardPosList (verts n) (G v)).mpr ⟨l, memVerts l, hvl⟩
  by_cases hd : degree G v = 1
  · exact (noAdjacentLeaves G hn hc hs hvl hd hdeg).elim
  · omega

theorem leMaxDegree {n} (G : Graph n) (S : Subset n) (v : Fin n)
    (h : S v = true) : degree G v ≤ maxDegreeIn G S := by
  have ih : ∀ (ys : List Nat) a, a ∈ ys → a ≤ ys.foldr max 0 := by
    intro ys
    induction ys with
    | nil => simp
    | cons b ys hys =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (hys a ha) (Nat.le_max_right _ _)
  have hh : degree G v ∈ (verts n).map (fun u => if S u then degree G u else 0) :=
    List.mem_map.mpr ⟨v, memVerts v, by simp [h]⟩
  exact ih _ _ hh

theorem sumMapScale {V : Type} (l : List V) (f : V → Nat) (k : Nat) :
    sumMap l (fun u => k * f u) = k * sumMap l f := by
  induction l with
  | nil => simp [sumMap]
  | cons a l ih =>
    simp only [sumMap,List.map_cons,List.sum_cons,Nat.mul_add] at *
    rw [ih]

theorem count_split_le {n} (U V W : Subset n)
    (hu : ∀ u, U u = true → W u = true) (hv : ∀ u, V u = true → W u = true)
    (hdis : ∀ u, U u = true → V u = false) :
    card U + card V ≤ card W := by
  unfold card
  rw [← sumMapAdd]
  apply sumMapMono
  intro u _
  cases hU : U u <;> cases hV : V u <;> simp_all [bit]

theorem bound {n} (G : Graph n) (hn : 2 < n) (hc : Connected G)
    (hs : ∀ x y, G x y = G y x) (D : Subset n) (hd : TotalDom G D) :
    card (isolatedIn G (neighbor G (support G))) ≤
      (maxDegreeIn G (support G) - 1) * card D := by
  let S := support G
  let N := neighbor G S
  let U := isolatedIn G N
  let I := isolatedIn G S
  let A : Subset n := fun v => U v && D v
  let B : Subset n := fun v => U v && !D v
  let k := maxDegreeIn G S - 1
  change card U ≤ k * card D
  have hsI (v : Fin n) (h : I v = true) : S v = true :=
    (Bool.and_eq_true _ _).mp h |>.1
  have hdI (v : Fin n) (h : I v = true) : D v = true :=
    supportForced G hs hd (hsI v h)
  have huN (v : Fin n) (h : U v = true) : N v = true :=
    (Bool.and_eq_true _ _).mp h |>.1
  have touchI (v : Fin n) (h : U v = true) : 0 < localCount G I v := by
    obtain ⟨w, hw, ha⟩ := (neighbor_iff G S v).mp (huN v h)
    have hj : (!(neighbor G N v)) = true := (Bool.and_eq_true _ _).mp h |>.2
    have hwN : N w = false := by
      cases hh : N w
      · rfl
      · have ht := (neighbor_iff G N v).mpr ⟨w,hh,ha⟩
        simp [ht] at hj
    have hI : I w = true := by
      change (S w && !(N w)) = true
      simp [hw,hwN]
    exact (local_pos_iff G I v).mpr ⟨w,hI,ha⟩
  have hcount1 : card B ≤ pairCount G B I := by
    unfold card
    rw [pairRows]
    apply sumMapMono
    intro v _
    cases hv : B v
    · simp [bit,hv]
    · have hu : U v = true := (Bool.and_eq_true _ _).mp hv |>.1
      have hh := touchI v hu
      simpa [bit,hv] using hh
  have hcount2 : pairCount G I B ≤ k*card I := by
    rw [pairRows]
    unfold card
    rw [← sumMapScale]
    apply sumMapMono
    intro v _
    cases hv : I v
    · simp [hv,bit]
    · have hdv := hd v
      have hdv2 := degreeSplit G D v
      have hdv3 := leMaxDegree G S v (hsI v hv)
      have hdv4 : localCount G B v ≤ localCount G (fun x => !D x) v := by
        unfold localCount card
        apply sumMapMono
        intro w _
        cases hu : U w <;> cases hb : D w <;> cases hg : G v w <;> simp [B,hu,hb,hg,bit]
      simp [hv,bit]
      omega
  rw [pairSwap G hs B I] at hcount1
  have hac : card A + card I ≤ card D := by
    apply count_split_le
    · intro v h
      exact (Bool.and_eq_true _ _).mp h |>.2
    · exact hdI
    · intro v h
      have hu : U v = true := (Bool.and_eq_true _ _).mp h |>.1
      have hnv := huN v hu
      change (S v && !(N v)) = false
      simp [hnv]
  have hsum := cardSplit U D
  change card U = card A + card B at hsum
  by_cases hz : card U = 0
  · simp [hz]
  · have hpos : 0 < card U := by omega
    obtain ⟨u, _, hu⟩ := (cardPosList (verts n) U).mp hpos
    obtain ⟨w,hw,_⟩ := (neighbor_iff G S u).mp (huN u hu)
    have hr := supportDegree G hn hc hs hw
    have hm := leMaxDegree G S w hw
    have hk : 1 ≤ k := by dsimp [k]; omega
    calc
      card U = card A + card B := hsum
      _ ≤ card A + k*card I := by omega
      _ ≤ k*card A + k*card I := by
        have := Nat.mul_le_mul_right (card A) hk
        simp at this
        omega
      _ = k * (card A + card I) := by rw [Nat.mul_add]
      _ ≤ k*card D := Nat.mul_le_mul_left k hac

/-- The exact cross-multiplied #381, for any minimum total-dominating-set
cardinality t. In fact the proof above works for every total dominating set,
and needs connectedness but not acyclicity. -/
theorem conjecture381 {n} (G : Graph n) (hn : 2 < n) (hc : Connected G)
    (hs : ∀ x y, G x y = G y x) (t : Nat)
    (ht : (∃ D, TotalDom G D ∧ card D = t) ∧ ∀ D, TotalDom G D → t ≤ card D) :
    card (isolatedIn G (neighbor G (support G))) ≤
      (maxDegreeIn G (support G) - 1) * t := by
  obtain ⟨D,hd,rfl⟩ := ht.1
  exact bound G hn hc hs D hd


theorem totalDom_exists_min {n} (G : Graph n) (hn : 2 < n) (hc : Connected G) :
    ∃ t, (∃ D, TotalDom G D ∧ card D = t) ∧ ∀ D, TotalDom G D → t ≤ card D := by
  have ht : TotalDom G (fun _ => true) := by
    intro u
    let v : Fin n := if u.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hv : u ≠ v := by
      intro e
      have ev := congrArg Fin.val e
      by_cases eu : u.val = 0 <;> simp [v,eu] at ev <;> omega
    have f : ∀ {a b}, a ≠ b → Walk G a b → 0 < localCount G (fun _ => true) a := by
      intro a b hab w
      cases w with
      | nil _ => exact (hab rfl).elim
      | @step _ z _ h _ => exact (local_pos_iff G _ _).mpr ⟨z,rfl,h⟩
    exact f hv (hc u v)
  classical
  have aux (k : Nat) (h : ∃ D, TotalDom G D ∧ card D = k) :
      ∃ t, (∃ D, TotalDom G D ∧ card D = t) ∧ ∀ D, TotalDom G D → t ≤ card D := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases hh : ∃ D, TotalDom G D ∧ card D < k
      · obtain ⟨D,hD,hk⟩ := hh
        exact ih (card D) hk ⟨D,hD,rfl⟩
      · exact ⟨k,h,fun D hD => Nat.le_of_not_gt (fun e => hh ⟨D,hD,e⟩)⟩
  exact aux (card (fun _ => true)) ⟨(fun _ => true),ht,rfl⟩

noncomputable def totalDominationNumber {n} (G : Graph n) (hn : 2 < n) (hc : Connected G) : Nat :=
  Classical.choose (totalDom_exists_min G hn hc)

theorem conjecture381_exact {n} (G : Graph n) (hn : 2 < n) (hc : Connected G)
    (hs : ∀ x y, G x y = G y x) :
    card (isolatedIn G (neighbor G (support G))) ≤
      (maxDegreeIn G (support G) - 1) * totalDominationNumber G hn hc :=
  conjecture381 G hn hc hs _ (Classical.choose_spec (totalDom_exists_min G hn hc))

#print axioms conjecture381_exact
end Graffiti381
