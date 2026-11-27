import PendantBounds
namespace Graffiti384b.PendantRank
open Finset SimpleGraph Donor
open private Donor.rankDegree from PendantBudget
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the two residual degree floors, exposed vertices and eligible edge
trials pay additive credits against a single explicit numerical threshold. -/
theorem weighted_frame (X : Finset V) (sz : X.card=26)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    {e : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e)
    (f : ℕ) (level : f=3 ∨ f=4) (degrees : ∀v∈X,f≤G.degree v)
    (Q : Finset (Finset V)) (valid : Usable G X Q)
    (paid : (if f=3 then 2785582 else 2150887)<
      (exposed G X).card*290000+(∑v∈X,marked G X v)+Q.card) :
    gamma G≤Fintype.card V-15 := by
  apply exact_from_mass G X sz inj pos ex outside degree f 290000 (by decide) (by omega) degrees Q valid
  have tab : (∑i∈range 26,envelope f 290000 i)=26*base+(if f=3 then 18720787 else 18086092) := by
    rcases level with rfl|rfl <;> unfold envelope charge reward base Donor.rankDegree FiniteRange.badCount <;>
      simp only [Nat.choose_eq_fast_choose] <;> decide
  rw [tab,show 3*(26:ℕ).choose 10=15935205 by decide]
  split_ifs at * <;> omega

/-- Four exposed vertices of degree at most four suffice at the unrestricted
floor. With minimum degree four in the pool, three such contacts suffice. -/
theorem small_contacts (X : Finset V) (sz : X.card=26) (highX : X⊆high G)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    {e : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e)
    (paid : let L := (exposed G X).filter (fun v => G.degree v≤4)
      4≤L.card ∨ 3≤L.card ∧ ∀v∈X,4≤G.degree v) :
    gamma G≤Fintype.card V-15 := by
  classical
  let L := (exposed G X).filter (fun v => G.degree v≤4)
  have sub : L⊆exposed G X := filter_subset ..
  have sx : L⊆X := sub.trans (filter_subset ..)
  have marks : L.card*591790 ≤ ∑v∈X,marked G X v := by
    have part := sum_le_sum_of_subset_of_nonneg sx (f:=marked G X) (fun v _ _ => Nat.zero_le _)
    have eq : (∑v∈L,marked G X v)=L.card*591790 := by
      rw [sum_congr rfl (fun v (vm : v∈L) => show marked G X v=591790 by
        simp only [marked,if_pos (sub vm),tariff,if_pos (mem_filter.mp vm).2])]
      simp
    rwa [eq] at part
  have count := card_le_card sub
  have valid : Usable G X ∅ := ⟨empty_subset _,by simp⟩
  rcases paid with four|⟨three,deg⟩
  · apply weighted_frame G X sz inj pos ex outside degree 3 (by decide)
      (fun v vm => (mem_filter.mp (highX vm)).2) ∅ valid
    change 4≤L.card at four
    change 2785582<(exposed G X).card*290000+(∑v∈X,marked G X v)+0
    omega
  · apply weighted_frame G X sz inj pos ex outside degree 4 (by decide) deg ∅ valid
    change 3≤L.card at three
    change 2150887<(exposed G X).card*290000+(∑v∈X,marked G X v)+0
    omega

end Graffiti384b.PendantRank
#print axioms Graffiti384b.PendantRank.weighted_frame
#print axioms Graffiti384b.PendantRank.small_contacts
