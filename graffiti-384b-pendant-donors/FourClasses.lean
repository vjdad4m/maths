import EdgeMass

namespace Graffiti384b.Donor
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With no fixed seeds the four neighborhood classes give the closed
binomial expression. For sample size b+1, A is the recipient's neighbors,
B its nonneighbors, d the donor-only count, and o the neither count.
The donor is outside X. The receiver is excluded from X in repair applications. -/
theorem four_classes (X : Finset V) (u v : V) (outside : v∉X) {b : ℕ} (pos : 0<b) :
    let A := X.filter (G.Adj u)
    let B := X.filter (fun z => ¬G.Adj u z)
    let d := nbr G v B
    let o := B.card-d
    (pairTrials G ∅ X (b+1) u v).card =
      A.card*o.choose b+(A.filter (fun z => ¬G.Adj v z)).card*d*o.choose (b-1) := by
  classical
  let A := X.filter (G.Adj u)
  let B := X.filter (fun z => ¬G.Adj u z)
  let d := nbr G v B
  let o := B.card-d
  change _=A.card*o.choose b+(A.filter (fun z => ¬G.Adj v z)).card*d*o.choose (b-1)
  have vb : v∉B := fun vm => outside (mem_filter.mp vm).1
  rw [zero_fixed G ∅ X (by simp) u v (by simp [nbr]) pos]
  have each (t : V) (tm : t∈A) : loss G (insert t ∅) B b v =
      o.choose b + if ¬G.Adj v t then d*o.choose (b-1) else 0 := by
    have vt : v≠t := fun eq => outside (eq ▸ (mem_filter.mp tm).1)
    by_cases adj : G.Adj v t
    · have c : nbr G v {t}=1 := by simp [nbr,filter_singleton,adj]
      simp [loss,vt,adj,erase_eq_of_not_mem vb,c,o,d]
    · have c : nbr G v {t}=0 := by simp [nbr,filter_singleton,adj]
      simp [loss,vt,adj,erase_eq_of_not_mem vb,c,o,d]
  change (∑ t∈A,loss G (insert t ∅) B b v)=_
  rw [sum_congr rfl each,sum_add_distrib,←sum_filter]
  simp [Nat.mul_assoc]

/-- The zero- and one-seed endpoints of the binomial formula. -/
theorem small_samples (X : Finset V) (u v : V) (out : v∉X) :
    (pairTrials G ∅ X 0 u v).card=0 ∧ (pairTrials G ∅ X 1 u v).card=nbr G u X := by
  classical
  constructor
  · simp [pairTrials,filter_singleton,nbr]
  · have eq : pairTrials G ∅ X 1 u v=(X.filter (G.Adj u)).image (fun z => {z}) := by
      ext k
      constructor
      · intro km
        obtain ⟨kp,recv,_⟩ := mem_filter.mp km
        obtain ⟨sub,sz⟩ := mem_powersetCard.mp kp
        obtain ⟨z,rfl⟩ := card_eq_one.mp sz
        have uz : G.Adj u z := by
          by_contra neg
          simp [nbr,filter_singleton,neg] at recv
        exact mem_image.mpr ⟨z,mem_filter.mpr ⟨sub (mem_singleton_self _),uz⟩,rfl⟩
      · intro km
        obtain ⟨z,zm,rfl⟩ := mem_image.mp km
        obtain ⟨zx,uz⟩ := mem_filter.mp zm
        have vz : v≠z := fun eq => out (eq ▸ zx)
        have low : nbr G v {z}<2 := by
          unfold nbr
          exact lt_of_le_of_lt (card_le_card (filter_subset ..)) (by simp)
        exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨singleton_subset_iff.mpr zx,card_singleton _⟩,
          by simp [nbr,filter_singleton,uz],mem_filter.mpr ⟨mem_univ _,by simpa using vz,by simpa using low⟩⟩
    rw [eq,card_image_of_injective _ (by intro a b h; simpa using h)]
    rfl

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.four_classes
#print axioms Graffiti384b.Donor.small_samples
