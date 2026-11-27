import LowEndpoint180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_exclusion (G : SimpleGraph V) {a b : V} (pair : TransPair G a b)
    (da : G.degree a≠4) (db : G.degree b≠4)
    (cheap : G.degree a/2+G.degree b/2≤PairBudget G a b) : ∀ K,¬PairCover G K := by
  intro K cover
  have rev : TransPair G b a := ⟨pair.1.symm,by simpa only [pair_comm b a] using pair.2⟩
  have bk := partner_forced G cover pair (fun solo => da solo.1)
  have ak := partner_forced G cover rev (fun solo => db solo.1)
  exact small_sum G pair cheap ((cover.2 _ _ pair).2.2 ak bk)

/-- Two distinct odd degrees, including a difference of exactly two, suffice
for all markings. No assumption on common neighbors is required. -/
theorem odd_degrees (G : SimpleGraph V) {a b : V} (pair : TransPair G a b)
    (da : Odd (G.degree a)) (db : Odd (G.degree b)) (ne : G.degree a≠G.degree b) :
    ∀ K,¬PairCover G K := by
  obtain ⟨i,hi⟩ := da
  obtain ⟨j,hj⟩ := db
  apply degree_exclusion G pair (by omega) (by omega)
  unfold PairBudget
  omega

theorem cubic_pair (G : SimpleGraph V) {a b : V} (pair : TransPair G a b)
    (da : G.degree a=3) (db : G.degree b=3) : ∀ K,¬PairCover G K :=
  low_endpoint G pair (by omega) (by omega)

#print axioms degree_exclusion
#print axioms cubic_pair
#print axioms odd_degrees
end Minimal180.PairRepair
