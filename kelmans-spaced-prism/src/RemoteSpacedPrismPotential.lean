import RemoteSpacedPrismOld

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSpacedPrismPotential
open RemoteSpacedPrismLayout
open RemoteSpacedPrismHandle (Port first)
open RemoteSpacedPrismOld (prior prior_packing vacancies slot_free)
open RemoteVacancySeparation (holes UnitPotential one_cleanup_separation_bound)
open RemoteVacancyReach (Packing Slides OneCleanup)

def colValue (k : Nat) : Board k→Nat
  | .inl v => v.1.val
  | .inr i => index i * gap k

def height (k : Nat) (v : Board k) : Nat :=
  min (colValue k v) (columns k-colValue k v)

private theorem hor_step {m a b : Nat} (ha : a<m) (hb : b<m)
    (edge : (a+1)%m=b) :
    min a (m-a) ≤ min b (m-b)+1 ∧ min b (m-b) ≤ min a (m-a)+1 := by
  by_cases h : a+1<m
  · rw [Nat.mod_eq_of_lt h] at edge
    omega
  · have w : a+1=m := by omega
    rw [w,Nat.mod_self] at edge
    omega

theorem unit_height (k : Nat) : UnitPotential (board k) (height k) := by
  rintro (x|i) (y|j) ed
  · have e : (core k).Adj x y := ed.1
    rcases e with ⟨_,hp|hp⟩|⟨xCol,_⟩
    · exact hor_step x.1.isLt y.1.isLt hp
    · exact (hor_step y.1.isLt x.1.isLt hp).symm
    · simp [height,colValue,xCol]
  · change (marks k).Ends j x at ed
    rcases ed with q|q
    · rw [q]
      simp [height,colValue,marks,markCol]
    · rw [q]
      simp [height,colValue,marks,markCol]
  · change (marks k).Ends i y at ed
    rcases ed with q|q
    · rw [q]
      simp [height,colValue,marks,markCol]
    · rw [q]
      simp [height,colValue,marks,markCol]
  · exact False.elim ed

def anchor (k : Nat) : Board k := Sum.inr (first false)

theorem anchor_vacant (k : Nat) : anchor k∈holes (prior k) :=
  slot_free k (first false)

theorem anchor_zero (k : Nat) : height k (anchor k)=0 := by
  simp [anchor,height,colValue,first,index]

theorem other_far (k : Nat) (x : Board k) (hx : x∈holes (prior k))
    (neq : x≠anchor k) : gap k≤height k x := by
  obtain ⟨i,rfl⟩ := (vacancies k x).mp hx
  have p : 1≤index i := by
    by_contra! x
    have h : index i=0 := by omega
    have h0 : index i=index (first false) := h
    exact neq (congrArg Sum.inr (index_injective h0))
  have q := index_lt6 i
  have low : gap k≤index i * gap k := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (gap k) p
  have hi : index i * gap k + gap k ≤ columns k := by
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right (gap k) (by omega)
  change gap k≤min (index i*gap k) (columns k-index i*gap k)
  omega

/-- No choice of final factor and no nonmonotone detour can meet a
bound B on this rank packing. The parameter B+2 makes the six slots
far enough apart. -/
theorem no_short_route (B : Nat) {Q F : Finset (Finset (Board (B+2)))}
    (hf : Packing (board (B+2)) F) (full : F.biUnion id=univ)
    {n : Nat} (nb : n≤B) (s : Slides n (prior (B+2)) Q) (c : OneCleanup Q F) :
    False := by
  have h := one_cleanup_separation_bound (prior_packing (B+2)) hf full (unit_height (B+2))
    (anchor_vacant (B+2)) (anchor_zero (B+2)) (gap (B+2)) (other_far (B+2)) s c
  simp only [gap] at h
  omega

#print axioms unit_height
#print axioms no_short_route
end KelmansCactus.AtomicBridge.RemoteSpacedPrismPotential
