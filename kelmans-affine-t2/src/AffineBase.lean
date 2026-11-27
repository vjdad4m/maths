import AffineKelmans

namespace KelmansCactus.AtomicBridge.AffineBase
open Finset

abbrev Point := KelmansAffine.Point
abbrev Line := KelmansAffine.Line
private abbrev Slot := Bool × Bool
abbrev Incident := KelmansAffine.Incident

/-- The natural four slope groups correspond bijectively to the four ports. -/
def slotSlope : Slot → Fin 4
  | (false,false) => 0
  | (false,true) => 1
  | (true,false) => 2
  | (true,true) => 3

def slopeSlot : Fin 4 → Slot := fun i =>
  if i.val = 0 then (false,false) else if i.val=1 then (false,true)
    else if i.val=2 then (true,false) else (true,true)

@[simp] theorem slopeSlot_slotSlope (s : Slot) : slopeSlot (slotSlope s) = s := by
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;> rfl

@[simp] theorem slotSlope_slopeSlot : ∀ i : Fin 4, slotSlope (slopeSlot i) = i := by decide

def routeSlope (p : Point) (s : Fin 4) : Line :=
  ⟨(3*s.val + (if s.val=3 then p.val/3
     else (p.val % 3 + 3 - (s.val*(p.val/3)) % 3) % 3)) % 12,
    Nat.mod_lt _ (by decide)⟩

/-- Each cell slot reaches its unique line of the designated slope. -/
def route (p : Point) (s : Slot) : Line := routeSlope p (slotSlope s)

private theorem routeSlope_inj :
    ∀ (p : Point) (i j : Fin 4), routeSlope p i = routeSlope p j → i=j := by decide

theorem route_injective (p : Point) : Function.Injective (route p) := by
  intro s t h
  have e := routeSlope_inj p _ _ h
  simpa using congrArg slopeSlot e

private theorem slope_incident :
    ∀ (p : Point) (l : Line), Incident p l ↔ ∃ i : Fin 4, routeSlope p i = l := by decide

theorem incident_iff_exists_slot (p : Point) (l : Line) :
    Incident p l ↔ ∃ s : Slot, route p s = l := by
  rw [slope_incident]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨slopeSlot i,by simpa [route,slotSlope_slopeSlot] using hi⟩
  · rintro ⟨s,hs⟩
    exact ⟨slotSlope s,hs⟩

theorem incident_iff (p : Point) (l : Line) :
    Incident p l ↔ ∃ s : Slot, route p s = l :=
  incident_iff_exists_slot p l

theorem card_points_on_line (l : Line) :
    (Finset.univ.filter (fun p => Incident p l)).card=3 :=
  KelmansAffine.control_degree l

theorem card_lines_on_point (p : Point) :
    (Finset.univ.filter (fun l => Incident p l)).card=4 :=
  KelmansAffine.cell_degree p

theorem distinct_points_unique_line (p q : Point) (h : p≠q) :
    ∃! l : Line, Incident p l ∧ Incident q l :=
  KelmansAffine.distinct_points_unique_line p q h

def remaining (except : Option Point) : Finset Point :=
  Finset.univ.filter (fun p => some p ≠ except)

@[simp] theorem mem_remaining {e : Option Point} {p : Point} :
    p ∈ remaining e ↔ some p ≠ e := by simp [remaining]

theorem remaining_has_eight (except : Option Point) : 8 ≤ (remaining except).card := by
  cases except with
  | none =>
    have h : remaining none = Finset.univ := by ext p; simp
    rw [h,Finset.card_univ]
    decide
  | some p =>
    have h : remaining (some p) = Finset.univ.erase p := by ext q; simp
    rw [h,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
    decide

theorem card_points_on_line_except (l : Line) (removed : Point) :
    2 ≤ (Finset.univ.filter (fun p => p≠removed ∧ Incident p l)).card := by
  have h : Finset.univ.filter (fun p => p≠removed ∧ Incident p l) =
      remaining (some removed) ∩ KelmansAffine.onLine l := by
    ext p
    simp
  rw [h]
  exact KelmansAffine.residual_control_degree _ (remaining_has_eight _) _

def MixedLine (c : Point → Bool) (except : Option Point) (l : Line) : Prop :=
  (∃ p : Point, some p ≠ except ∧ Incident p l ∧ c p = true) ∧
  (∃ p : Point, some p ≠ except ∧ Incident p l ∧ c p = false)

instance (c : Point → Bool) (except : Option Point) (l : Line) :
    Decidable (MixedLine c except l) := by unfold MixedLine; infer_instance

lemma mixed_line_iff_mem_filter (c : Point → Bool) (except : Option Point) (l : Line) :
    MixedLine c except l ↔ l ∈ KelmansAffine.mixedLines (remaining except) c := by
  unfold MixedLine KelmansAffine.mixedLines
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.Nonempty,
    KelmansAffine.redOn,KelmansAffine.blueOn,Finset.mem_inter,KelmansAffine.redPoints,
    KelmansAffine.bluePoints,mem_remaining,KelmansAffine.mem_onLine]
  constructor
  · rintro ⟨⟨p,hp,ep,cp⟩,⟨q,hq,eq,cq⟩⟩
    exact ⟨⟨p,⟨hp,cp⟩,ep⟩,⟨q,⟨hq,cq⟩,eq⟩⟩
  · rintro ⟨⟨p,⟨hp,cp⟩,ep⟩,⟨q,⟨hq,cq⟩,eq⟩⟩
    exact ⟨⟨p,hp,ep,cp⟩,⟨q,hq,eq,cq⟩⟩

/-- Splitting the active points into two nonempty color classes exposes at
least four mixed lines, even after deleting one point. -/
theorem mixed_at_least_four (c : Point → Bool) (except : Option Point)
    (hr : ∃ p : Point, some p ≠ except ∧ c p=true)
    (hb : ∃ p : Point, some p ≠ except ∧ c p=false) :
    4 ≤ (Finset.univ.filter (MixedLine c except)).card := by
  have h : Finset.univ.filter (MixedLine c except) =
      KelmansAffine.mixedLines (remaining except) c := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact mixed_line_iff_mem_filter _ _ _
  rw [h]
  apply KelmansAffine.card_mixed_ge_four _ _ (remaining_has_eight except)
  · obtain ⟨p,hp,hc⟩ := hr
    exact ⟨p,Finset.mem_filter.mpr ⟨mem_remaining.mpr hp,hc⟩⟩
  · obtain ⟨p,hp,hc⟩ := hb
    exact ⟨p,Finset.mem_filter.mpr ⟨mem_remaining.mpr hp,hc⟩⟩

#print axioms route_injective
#print axioms incident_iff_exists_slot
#print axioms card_points_on_line_except
#print axioms distinct_points_unique_line
#print axioms mixed_at_least_four
end KelmansCactus.AtomicBridge.AffineBase
