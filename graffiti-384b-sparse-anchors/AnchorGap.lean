import SparseFrontier
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph JointRank
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
/-- If one anchor has triangle count two, every other anchor has count at
least fifteen throughout the 31-nonleaf profile. -/
theorem anchor_score_gap (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    {w : V} (wa : w∈G.neighborFinset e∪G.neighborFinset f) (sc : trianglesAt G w=2) :
    ∀ a∈G.neighborFinset e∪G.neighborFinset f,a≠w → 15≤trianglesAt G a := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let E := LowSample.twos G
  let r := rank (high G) (trianglesAt G)
  let c := fun a => credit (r a)
  obtain ⟨_,ah,ac,_,_,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  have inE {u : V} (du : G.degree u=2) : u∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have eq : ({e,f}:Finset V)=E := eq_of_subset_of_card_le (insert_subset (inE de) (singleton_subset_iff.mpr (inE df)))
    (by rw [card_pair ef]; exact es.le)
  have full : E.biUnion (G.neighborFinset ·)=A := by rw [←eq]; simp [A]
  obtain ⟨u,um,uw⟩ := mem_biUnion.mp (show w∈E.biUnion (G.neighborFinset ·) from full.symm ▸ wa)
  have total := two_score_budget G t q bad um ((G.mem_neighborFinset ..).mp uw) sc
  change 3124550+(∑a∈E.biUnion (G.neighborFinset ·),c a)≤12407000 at total
  rw [full] at total
  obtain ⟨inj,lo,_,_⟩ := Repair.maximal_diversity G (by omega)
  have ranks (a : V) (aa : a∈A) : r a<29 ∧ 2+r a≤trianglesAt G a := by
    have h := mem_image_of_mem (rank (high G) (trianglesAt G)) (ah aa)
    rw [rank_range _ _ inj,hs,mem_range] at h
    exact ⟨h,rank_lower _ _ inj 2 lo (ah aa)⟩
  have tab : ∀ i : Fin 29,739024≤credit i ∧ (i.val≤12 → 3233230≤credit i) := by unfold credit; decide
  have rw' := ranks w wa
  have w0 : r w=0 := by omega
  have cw : c w=4975245 := by simp [c,w0,credit]
  intro a aa aw
  apply Nat.le_of_not_gt; intro neg
  have ar := ranks a aa
  have ca := (tab ⟨r a,ar.1⟩).2 (by dsimp only; omega)
  change 3233230≤c a at ca
  have am : a∈A.erase w := mem_erase.mpr ⟨aw,aa⟩
  let S := (A.erase w).erase a
  have sz : S.card=2 := by dsimp [S]; rw [card_erase_of_mem am,card_erase_of_mem wa,show A.card=4 from ac]
  have rest : (∑ _i∈S,739024)≤∑i∈S,c i := sum_le_sum (fun i im =>
    (tab ⟨r i,(ranks i (mem_erase.mp (mem_erase.mp im).2).2).1⟩).1)
  rw [sum_const,sz,smul_eq_mul] at rest
  have s1 := sum_erase_add A c wa
  have s2 := sum_erase_add (A.erase w) c am; change (∑i∈S,c i)+c a=_ at s2
  omega
/-- The catalogue inequality holds through seven distinct exterior contacts. -/
theorem at_most_seven (t : (types G).card=31) (q : (nonleaves G).card=31)
    {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (sparse : (((high G)\(G.neighborFinset e∪G.neighborFinset f)).filter
      (fun i => 0<nbr G i (G.neighborFinset e∪G.neighborFinset f))).card≤7) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  have lim := (sparse_frontier G t q bad ef de df).1
  omega

end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.anchor_score_gap
#print axioms Graffiti384b.SparsePairs.at_most_seven
