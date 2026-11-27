import FragmentFlankRules

namespace Graffiti199Depleted.WiderOmission

open CompactOmission (SixTree)

inductive FragmentChoice (n k t : ℕ)
  | tree (order : Fin 6 → Fin ((n+1)+t))
  | route (route : FragmentRoute n k)
  | keep

def FragmentChoice.Valid {n k t : ℕ} (ext : Fin ((n+1)+t) → Fin ((n+1)+t) → Bool)
    (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (routeRule : FragmentRoute n k → Prop) (keepRule : Prop)
    (c : FragmentChoice n k t) : Prop :=
  match c with
  | .tree order => SixTree ext order
  | .route r => r.Valid D e ∧ routeRule r
  | .keep => keepRule

instance fragmentChoiceValidDecidable {n k t : ℕ} (ext : Fin ((n+1)+t) → Fin ((n+1)+t) → Bool)
    (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (routeRule : FragmentRoute n k → Prop) (keepRule : Prop)
    [∀ r, Decidable (routeRule r)] [Decidable keepRule] (c : FragmentChoice n k t) :
    Decidable (c.Valid ext D e routeRule keepRule) := by
  cases c <;> unfold FragmentChoice.Valid <;> infer_instance

theorem FragmentChoice.sound {n k t : ℕ} {ext : Fin ((n+1)+t) → Fin ((n+1)+t) → Bool}
    {D : Seams n k} {e : Fin (n+1) → Fin (n+1) → Bool}
    {routeRule : FragmentRoute n k → Prop} {keepRule : Prop}
    {c : FragmentChoice n k t} (h : c.Valid ext D e routeRule keepRule) :
    (∃ T, SixTree ext T) ∨ (∃ r, r.Valid D e ∧ routeRule r) ∨ keepRule := by
  cases c with
  | tree T => exact Or.inl ⟨T,h⟩
  | route r => exact Or.inr (Or.inl ⟨r,h⟩)
  | keep => exact Or.inr (Or.inr h)

def LeftRoutes {n k : ℕ} (b : Layout n) (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (P : List ℕ) (cert : ℕ → FragmentRoute n k) : Prop :=
  ¬ BlocksFirst b e → ∀ i : Fin P.length, touch (P.get i) (rightEnd n) = true →
    (cert (P.get i)).Valid D e ∧ touch (P.get i) (cert (P.get i)).last = true

def RightRoutes {n k : ℕ} (b : Layout n) (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (P : List ℕ) (cert : ℕ → FragmentRoute n k) : Prop :=
  ¬ BlocksLast b e → ∀ i : Fin P.length, touch (P.get i) (0 : Fin (n+1)) = true →
    (cert (P.get i)).Valid D e ∧ touch (P.get i) (cert (P.get i)).first = true

def PairChecks {n k : ℕ} (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (P : List ℕ) (lm rm : ℕ) (link : Bool) (cert : ℕ → ℕ → Bool → FragmentChoice n k 2) : Prop :=
  ∀ (i j : Fin P.length) (b : Bool), let a := P.get i; let d := P.get j
    touch a (0 : Fin (n+1)) = true → touch d (rightEnd n) = true →
    (cert a d b).Valid (pairEdge e a d b) D e
      (fun r => touch a r.first = true ∧ touch d r.last = true) (a = lm ∧ d = rm ∧ b = link)

def StepChecks {n k : ℕ} (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (P : List ℕ) (lm rm : ℕ) (link : Bool) (cert : ℕ → Bool → FragmentChoice n k 3) : Prop :=
  lm ∈ P → rm ∈ P → ∀ (i : Fin P.length) (b : Bool), let m := P.get i
    (cert m b).Valid (fragmentStepEdge e lm rm m link b) D e
     (fun r => (touch lm r.first = true ∧ touch rm r.last = true) ∨
       (touch m r.first = true ∧ touch lm r.last = true ∧ link = true)) (m = lm ∧ b = link)

def flanks_from_checks {n k : ℕ} (b : Layout n) (D : Seams n k)
    (e : Fin (n+1) → Fin (n+1) → Bool) (mate : Fin (n+1))
    (P : List ℕ) (lm rm : ℕ) (link : Bool)
    (single : SingleChecks e mate P) (stop : ∃ i, touch lm (b.next i) = true)
    (someFlank : BlocksFirst b e ∨ BlocksLast b e)
    {lc rc : ℕ → FragmentRoute n k} {pc : ℕ → ℕ → Bool → FragmentChoice n k 2}
    {sc : ℕ → Bool → FragmentChoice n k 3}
    (l : LeftRoutes b D e P lc) (r : RightRoutes b D e P rc)
    (pair : PairChecks D e P lm rm link pc) (step : StepChecks D e P lm rm link sc) :
    FragmentFlanks n k b e D mate where
  profiles := P
  single := single
  lmask := lm
  rmask := rm
  linked := link
  stop := stop
  someFlank := someFlank
  leftEmpty := by
    intro empty m hm edge
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
    exact ⟨_,l empty i edge⟩
  rightEmpty := by
    intro empty m hm edge
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
    exact ⟨_,r empty i edge⟩
  pair := by
    intro a d link ha hd ea ed
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hd
    exact FragmentChoice.sound (pair i j link ea ed)
  advance := by
    intro hl hr m b hm
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
    exact FragmentChoice.sound (step hl hr i b)

end Graffiti199Depleted.WiderOmission
