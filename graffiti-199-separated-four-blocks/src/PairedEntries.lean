import RetainedGeometry

namespace Graffiti199Depleted

open SimpleGraph

/-- A lost label is an admissible entry if its opposite half still
has a retained tip. -/
def pairGoodEntries (lost : Finset O) : Finset O :=
  lost.filter fun i => 2 ≤ i.val ∧
    (if i.val < 4 then (4 : O) ∉ lost ∨ (5 : O) ∉ lost else (2 : O) ∉ lost ∨ (3 : O) ∉ lost)

theorem pairGoodEntries_subset (lost : Finset O) : pairGoodEntries lost ⊆ lost :=
  Finset.filter_subset _ _

/-- With two or three losses, each in a high label, the pair has at
least two admissible lost entries. -/
theorem pairGoodEntries_two (lost : Finset O) (high : ∀ i ∈ lost, 2 ≤ (i : O).val)
    (two : 2 ≤ lost.card) (three : lost.card ≤ 3) : 2 ≤ (pairGoodEntries lost).card := by
  revert lost
  decide

/-- For one loss, that label is admissible. For three losses, exactly
two labels are admissible, and the third sees the unique retained tip. -/
theorem pairGoodEntries_of_single_loss (lost : Finset O) (high : ∀ i ∈ lost, 2 ≤ (i : O).val)
    (one : lost.card = 1) : pairGoodEntries lost = lost := by
  revert lost
  decide

theorem pairGoodEntries_card_of_three (lost : Finset O) (high : ∀ i ∈ lost, 2 ≤ (i : O).val)
    (three : lost.card = 3) : (pairGoodEntries lost).card = 2 := by
  revert lost
  decide

private theorem distinct_high_contacts :
    ∀ i j : O, 2 ≤ i.val → 2 ≤ j.val → i ≠ j →
      terminalHas i j = true ∨
        (if i.val < 4 then j = 4 ∨ j = 5 else j = 2 ∨ j = 3) := by decide

theorem nonentry_sees_retained (lost : Finset O) {i j : O}
    (iHi : 2 ≤ i.val) (iLost : i ∈ lost) (iBad : i ∉ pairGoodEntries lost)
    (jHi : 2 ≤ j.val) (jKeep : j ∉ lost) : terminalHas i j = true := by
  have ne : i ≠ j := fun eq => jKeep (eq ▸ iLost)
  rcases distinct_high_contacts i j iHi jHi ne with edge|opposite
  · exact edge
  exfalso
  apply iBad
  apply Finset.mem_filter.mpr
  refine ⟨iLost,iHi,?_⟩
  by_cases left : i.val < 4
  · simp only [left, if_true] at opposite ⊢
    exact opposite.elim (fun e => Or.inl (e ▸ jKeep)) (fun e => Or.inr (e ▸ jKeep))
  · simp only [left, if_false] at opposite ⊢
    exact opposite.elim (fun e => Or.inl (e ▸ jKeep)) (fun e => Or.inr (e ▸ jKeep))

private def pairEntryRoute (lost : Finset O) (i : O) : List O :=
  (if i.val < 4 then [2,3,0,1,4,5] else [4,5,1,0,2,3]).filter (fun v => decide (v ∉ lost))

private theorem entry_cert (lost : Finset O) (onlyHigh : ∀ i ∈ lost, 2 ≤ (i : O).val)
    {i : O} (ok : i ∈ pairGoodEntries lost) :
    let xs := pairEntryRoute lost i
    xs.Nodup ∧ (∀ k, k ∈ xs ↔ k ∉ lost) ∧ xs.Chain' (fun a b => terminalHas a b = true) ∧
      ∃ a b : O, xs.head? = some a ∧ terminalHas i a = true ∧ xs.getLast? = some b ∧
        2 ≤ b.val ∧ b ∉ lost := by
  revert lost i
  decide

variable {V : Type*} {G : SimpleGraph V}

def PathOn.rev {U : Set V} (p : PathOn G U) : PathOn G U :=
  ⟨p.vertices.reverse,fun h => p.nonempty (List.reverse_eq_nil_iff.mp h),
    List.chain'_reverse.mpr (p.chain.imp (fun _ _ e => e.symm)),
    List.nodup_reverse.mpr p.nodup,fun v => (List.mem_reverse).trans (p.covers v)⟩

@[simp] theorem PathOn.rev_first {U : Set V} (p : PathOn G U) : p.rev.first = p.last :=
  List.head_reverse p.rev.nonempty

@[simp] theorem PathOn.rev_last {U : Set V} (p : PathOn G U) : p.rev.last = p.first :=
  List.getLast_reverse p.rev.nonempty

@[simp] theorem PathOn.join_last {U W : Set V} (p : PathOn G U) (q : PathOn G W)
    (dis : Disjoint U W) (edge : G.Adj p.last q.first) : (p.join q dis edge).last = q.last :=
  List.getLast_append_of_ne_nil (p.join q dis edge).nonempty q.nonempty

variable [Fintype V] [DecidableRel G.Adj]

/-- Traverse the retained pair starting from an edge at an admissible
lost entry. The final vertex is a retained high. -/
theorem FourBlockPacking.path_at_good_entry (F : FourBlockPacking G) (P : FullPair G)
    {i : O} (good : i ∈ pairGoodEntries (F.lost P)) :
    ∃ p : PathOn G (F.retained P), G.Adj (P.f i) p.first ∧
      ∃ j : O, 2 ≤ j.val ∧ j ∉ F.lost P ∧ p.last = P.f j := by
  let xs := pairEntryRoute (F.lost P) i
  obtain ⟨nd,cover,chain,a,b,aFirst,ia,bLast,bHi,bKeep⟩ :=
    entry_cert (F.lost P) (fun k m => (F.mem_lost.mp m).1) good
  have one {u v : O} (h : terminalHas u v = true) : G.Adj (P.f u) (P.f v) := by
    simp only [terminalHas,Bool.or_eq_true,List.contains_iff_mem] at h
    exact h.elim (P.edges _ _) (fun m => (P.edges _ _ m).symm)
  have nonempty : xs ≠ [] := by
    intro e
    change xs.head? = some a at aFirst
    simp [e] at aFirst
  let p : PathOn G (F.retained P) :=
    liftLabelPath P.f xs nonempty nd (chain.imp (fun _ _ h => one h)) cover
  have first : p.first = P.f a := by
    apply Option.some.inj
    change some (p.vertices.head p.nonempty) = some (P.f a)
    rw [← List.head?_eq_head p.nonempty]
    change (xs.map P.f).head? = _
    simp [show xs.head? = some a from aFirst]
  have last : p.last = P.f b := by
    apply Option.some.inj
    change some (p.vertices.getLast p.nonempty) = some (P.f b)
    rw [← List.getLast?_eq_getLast p.nonempty]
    change (xs.map P.f).getLast? = _
    simp [show xs.getLast? = some b from bLast]
  exact ⟨p,first.symm ▸ one ia,b,bHi,bKeep,last⟩

#print axioms pairGoodEntries_two
#print axioms pairGoodEntries_of_single_loss
#print axioms pairGoodEntries_card_of_three
#print axioms nonentry_sees_retained
#print axioms FourBlockPacking.path_at_good_entry

end Graffiti199Depleted
