import AnchorGap
import SparseEight
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph JointRank
open private SparsePairs.row from SparseRanks
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle-count-two ear neighbor has degree at most four in a failure. -/
theorem score_two_degree_le_four (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    {w : V} (wa : w∈G.neighborFinset e∪G.neighborFinset f) (sc : trianglesAt G w=2) : G.degree w≤4 := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let E := LowSample.twos G
  let r := rank (high G) (trianglesAt G)
  let c := fun a => augmented (r a) (G.degree a)
  obtain ⟨_,ah,ac,_,_,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  have inE {u : V} (du : G.degree u=2) : u∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have eq : ({e,f}:Finset V)=E := eq_of_subset_of_card_le (insert_subset (inE de) (singleton_subset_iff.mpr (inE df)))
    (by rw [card_pair ef]; exact es.le)
  have full : E.biUnion (G.neighborFinset ·)=A := by rw [←eq]; simp [A]
  have total := rank_account G t q bad 0 (base_mass G t q bad)
  change 0+(∑ a∈E.biUnion (G.neighborFinset ·),c a)≤12407000 at total
  rw [full] at total
  obtain ⟨inj,lo,_,_⟩ := Repair.maximal_diversity G (by omega)
  have w0 : r w=0 := by have h := rank_lower _ _ inj 2 lo (ah wa); change 2+r w≤_ at h; omega
  have tab : ∀ i : Fin 29,739024≤credit i := by unfold credit; decide
  have rest := sum_le_sum (s:=A.erase w) (fun a am => by
    have h := mem_image_of_mem (rank (high G) (trianglesAt G)) (ah (mem_erase.mp am).2)
    rw [rank_range _ _ inj,hs,mem_range] at h
    exact (tab ⟨r a,h⟩).trans (credit_le_augmented (r a) (G.degree a)))
  change (∑ _a∈A.erase w,739024)≤∑a∈A.erase w,c a at rest
  rw [sum_const,card_erase_of_mem wa,show A.card=4 from ac,smul_eq_mul] at rest
  have split := sum_erase_add A c wa
  by_contra! large
  have cap := Nat.choose_le_choose 11 (show 29-min (G.degree w) 10≤24 by omega)
  rw [show (24:ℕ).choose 11=2496144 by decide] at cap
  have price := le_max_right (credit 0+if 0=0 ∧ 4≤G.degree w then 3124550 else 0)
    (SparsePairs.row 0-(29-min (G.degree w) 10).choose 11)
  change SparsePairs.row 0-_≤augmented 0 (G.degree w) at price
  rw [show SparsePairs.row 0=12701405 by decide,←w0] at price
  change _≤c w at price
  omega

end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.score_two_degree_le_four
