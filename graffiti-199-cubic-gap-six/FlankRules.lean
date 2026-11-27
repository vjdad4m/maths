import WidePlacement

namespace Graffiti199Depleted.WiderOmission

open CompactOmission (SixTree)

def rightEnd (n : ℕ) : Fin (n+1) := ⟨n-1,by omega⟩

def touch {n : ℕ} (mask : ℕ) (i : Fin (n+1)) : Bool := mask.testBit i.val

def extension {n k : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (m : Fin k → ℕ)
    (links : Fin k → Fin k → Bool) : Fin ((n+1)+k) → Fin ((n+1)+k) → Bool :=
  Fin.addCases (fun i => Fin.addCases (e i) (fun j => touch (m j) i))
    (fun i => Fin.addCases (touch (m i)) (links i))

def singleLinks : Fin 1 → Fin 1 → Bool := fun _ _ => false
def pairLinks (b : Bool) : Fin 2 → Fin 2 → Bool := fun i j => (i != j) && b
def stepLinks (b : Bool) : Fin 3 → Fin 3 → Bool :=
  fun i j => (i != j) && (i == 0 || j == 0 || b)

def pairOrder {n : ℕ} (P : List (Fin (n+1))) : List (Fin ((n+1)+2)) :=
  Fin.natAdd (n+1) (0 : Fin 2) :: P.map (Fin.castAdd 2) ++ [Fin.natAdd (n+1) (1 : Fin 2)]

def stepOrder {n : ℕ} (P : List (Fin (n+1))) (front : Bool) : List (Fin ((n+1)+3)) :=
  let l := Fin.natAdd (n+1) (0 : Fin 3)
  let r := Fin.natAdd (n+1) (1 : Fin 3)
  let y := Fin.natAdd (n+1) (2 : Fin 3)
  if front then y :: l :: P.map (Fin.castAdd 3) ++ [r] else y :: P.map (Fin.castAdd 3) ++ [l,r]

def PairRoute {n : ℕ} (e : Fin ((n+1)+2) → Fin ((n+1)+2) → Bool)
    (P : List (Fin (n+1))) : Prop :=
  P.Perm (List.finRange (n+1)) ∧ (pairOrder P).Chain' (fun i j => e i j = true)

def StepRoute {n : ℕ} (e : Fin ((n+1)+3) → Fin ((n+1)+3) → Bool)
    (P : List (Fin (n+1))) (front : Bool) : Prop :=
  P.Perm (List.finRange (n+1)) ∧ (stepOrder P front).Chain' (fun i j => e i j = true)

instance {n : ℕ} (e : Fin ((n+1)+2) → Fin ((n+1)+2) → Bool) (P : List (Fin (n+1))) :
    Decidable (PairRoute e P) := by unfold PairRoute; infer_instance

instance {n : ℕ} (e : Fin ((n+1)+3) → Fin ((n+1)+3) → Bool) (P : List (Fin (n+1))) (front : Bool) :
    Decidable (StepRoute e P front) := by unfold StepRoute; infer_instance

def singleEdge {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (m : ℕ) :
    Fin ((n+1)+1) → Fin ((n+1)+1) → Bool :=
  extension e (fun _ : Fin 1 => m) singleLinks

def pairEdge {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (m n' : ℕ) (b : Bool) :
    Fin ((n+1)+2) → Fin ((n+1)+2) → Bool :=
  extension e (![m,n'] : Fin 2 → ℕ) (pairLinks b)

def stepEdge {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (boundary m : ℕ) (b : Bool) :
    Fin ((n+1)+3) → Fin ((n+1)+3) → Bool :=
  extension e (![boundary,boundary,m] : Fin 3 → ℕ) (stepLinks b)

structure FlankRules (n : ℕ) (e : Fin (n+1) → Fin (n+1) → Bool) (mate : Fin (n+1)) where
  profiles : List ℕ
  boundary : ℕ
  outerChord : e 0 (rightEnd n) = true
  boundaryRight : touch boundary (rightEnd n) = true
  single : ∀ row, touch row (Fin.last n) = false → touch row mate = false →
    (∃ T, SixTree (singleEdge e row) T) ∨
      ∃ r ∈ profiles, ∀ i : Fin (n+1), touch row i = touch r i
  pair : ∀ m q b, m ∈ profiles → q ∈ profiles → touch m (0 : Fin (n+1)) = true →
    touch q (rightEnd n) = true →
    (∃ T, SixTree (pairEdge e m q b) T) ∨ (∃ P, PairRoute (pairEdge e m q b) P) ∨
      (m = boundary ∧ q = boundary ∧ b = true)
  step : ∀ m b, m ∈ profiles →
    (∃ T, SixTree (stepEdge e boundary m b) T) ∨
      (∃ P front, StepRoute (stepEdge e boundary m b) P front) ∨
      (m = boundary ∧ b = true)

def singlePattern {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) : Pattern ((n+1)+1) where
  fixed := singleEdge e 0
  slot :=
    Fin.addCases (fun i : Fin (n+1) => Fin.addCases (fun _ : Fin (n+1) => none)
      (fun _ : Fin 1 => some i.val))
      (fun _ : Fin 1 => Fin.addCases (fun i : Fin (n+1) => some i.val) (fun _ : Fin 1 => none))

theorem single_pattern_edge {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (row : ℕ) :
    (singlePattern e).edge row = singleEdge e row := by
  funext i j
  revert j
  refine Fin.addCases ?_ ?_ i
  · intro u j
    refine Fin.addCases ?_ ?_ j
    · intro v
      simp [Pattern.edge,singlePattern,singleEdge,extension,Fin.addCases_left]
    · intro v
      simp [Pattern.edge,singlePattern,singleEdge,extension,touch,Fin.addCases_left,Fin.addCases_right]
  · intro u j
    refine Fin.addCases ?_ ?_ j
    · intro v
      simp [Pattern.edge,singlePattern,singleEdge,extension,touch,Fin.addCases_left,Fin.addCases_right]
    · intro v
      simp [Pattern.edge,singlePattern,singleEdge,extension,Fin.addCases_right]

def ProfileKnown {n : ℕ} (good : List ℕ) (d v t : ℕ) : Prop :=
  t ∈ good ∧ v = t ∧ ∀ i : Fin (n+1), d.testBit i.val = true

instance {n : ℕ} (good : List ℕ) (d v t : ℕ) : Decidable (ProfileKnown (n := n) good d v t) := by
  unfold ProfileKnown
  infer_instance

theorem certify_single {n : ℕ} {e : Fin (n+1) → Fin (n+1) → Bool} {mate : Fin (n+1)}
    {good : List ℕ} {C : Cover ((n+1)+1)}
    (valid : C.Valid (singlePattern e) (ProfileKnown (n := n) good)
      (2^n ||| 2^mate.val) 0) (row : ℕ)
    (hz : touch row (Fin.last n) = false) (hm : touch row mate = false) :
    (∃ T, SixTree (singleEdge e row) T) ∨
      ∃ r ∈ good, ∀ i : Fin (n+1), touch row i = touch r i := by
  have agrees : Agree row (2^n ||| 2^mate.val) 0 := by
    intro b kb
    have k : n = b ∨ mate.val = b := by
      simpa [Nat.testBit_or,Nat.testBit_two_pow] using kb
    rcases k with rfl|rfl
    · simpa [touch] using hz
    · simpa [touch] using hm
  rcases Cover.sound valid agrees with h|⟨dom,val,t,a,ok,eq,known⟩
  · rw [single_pattern_edge] at h
    exact Or.inl h
  · subst val
    exact Or.inr ⟨t,ok,fun i => a i.val (known i)⟩

end Graffiti199Depleted.WiderOmission
