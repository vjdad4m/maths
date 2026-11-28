import EarRepresentatives
namespace Graffiti384b.OddStars.CollisionBudget
open Finset SimpleGraph PositivePalette EarPacking EarFootprint EarRepresentatives
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def exceptional := (rich G).filter (fun v => EarTriangleLoss.inside G v+1<trianglesAt G v)
def loss (v : V) := trianglesAt G v-EarTriangleLoss.inside G v

omit [Fintype V] [DecidableEq V] in
theorem sum_nbr (S T : Finset V) : (∑x∈S,nbr G x T)=∑y∈T,nbr G y S := by
  classical
  have single (v : V) (B : Finset V) : nbr G v B=∑w∈B,if G.Adj v w then 1 else 0 := by
    rw [←sum_filter]; simp [nbr]
  simp_rw [single]
  rw [sum_comm]
  apply sum_congr rfl; intro v _
  apply sum_congr rfl; intro w _
  by_cases e : G.Adj v w
  · simp [e,e.symm]
  · simp [e,show ¬G.Adj w v from fun z => e z.symm]

theorem loss_eq {F : Finset V} (rep : EarRepresentatives.Represents G F) {v : V} (vm : v∈rich G) :
    loss G v=nbr (patch G ∅) v F := by
  rw [loss,score_eq G rep vm,Nat.add_sub_cancel_left]

private theorem incidences (F : Finset V) (rep : EarRepresentatives.Represents G F) :
    (anchors G F).card+(exceptional G).card≤∑f∈F,nbr (patch G ∅) f (rich G) := by
  classical
  let J := patch G ∅
  let A := anchors G F
  let E := exceptional G
  have eqA : A=(rich G).filter (fun v => 0<nbr J v F) := by
    ext v; constructor
    · intro m; obtain ⟨un,vr⟩ := mem_inter.mp m
      obtain ⟨f,fm,vf⟩ := mem_biUnion.mp un
      exact mem_filter.mpr ⟨vr,card_pos.mpr ⟨f,mem_filter.mpr ⟨fm,((J.mem_neighborFinset ..).mp vf).symm⟩⟩⟩
    · intro m; obtain ⟨vr,count⟩ := mem_filter.mp m
      obtain ⟨f,fm⟩ := card_pos.mp count
      obtain ⟨ff,vf⟩ := mem_filter.mp fm
      exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨f,ff,(J.mem_neighborFinset ..).mpr vf.symm⟩,vr⟩
  have eqE : E=(rich G).filter (fun v => 2≤nbr J v F) := by
    ext v; simp only [E,exceptional,mem_filter]
    constructor <;> rintro ⟨vr,b⟩ <;> have s := score_eq G rep vr <;> exact ⟨vr,by change trianglesAt G v=EarTriangleLoss.inside G v+nbr J v F at s; omega⟩
  have indic (P : V→Prop) [DecidablePred P] : (∑v∈rich G,if P v then 1 else 0)=((rich G).filter P).card := by
    rw [←sum_filter]; simp
  have less : (∑v∈rich G, ((if 0<nbr J v F then 1 else 0)+(if 2≤nbr J v F then 1 else 0)))≤∑v∈rich G,nbr J v F := by
    apply sum_le_sum; intro v _; split_ifs <;> omega
  rw [sum_add_distrib,indic,indic,←eqA,←eqE,sum_nbr J] at less
  exact less

private theorem available {F : Finset V} (rep : EarRepresentatives.Represents G F) (f : V) (fm : f∈F) :
    nbr (patch G ∅) f (rich G)≤2 := by
  let J := patch G ∅
  have hi := card_le_card (show (rich G).filter (J.Adj f)⊆J.neighborFinset f from fun _ m =>
    (J.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
  rw [card_neighborFinset_eq_degree,show J.degree f=2 from one_degree G (rep.one f fm)] at hi
  exact hi

/-- In a catalogue failure, at most one rich vertex loses two incident
triangles. Every other rich vertex loses at most one. -/
theorem at_most_one (bad : bound G<gamma G) : (exceptional G).card≤1 := by
  classical
  obtain ⟨F,rep⟩ := exists_representatives G
  by_cases present : 1∈types G
  · have need := (matching_profile G bad present rep.one rep.independent).1
    have count := incidences G F rep
    have cap : (∑f∈F,nbr (patch G ∅) f (rich G))≤∑_f∈F,2 := sum_le_sum (available G rep)
    simp only [sum_const,Nat.nsmul_eq_mul] at cap
    omega
  · have empty : F=∅ := by
      apply subset_empty.mp
      intro f fm
      exact (present (mem_image.mpr ⟨f,mem_univ _,rep.one f fm⟩)).elim
    have ct := incidences G F rep
    rw [empty,sum_empty] at ct
    omega

/-- A double loss exhausts the one-incidence allowance. Every chosen
ear then has both its triangle neighbors in the rich core. -/
theorem saturated (bad : bound G<gamma G) {F : Finset V} (rep : EarRepresentatives.Represents G F)
    (non : (exceptional G).Nonempty) (f : V) (fm : f∈F) : nbr (patch G ∅) f (rich G)=2 := by
  classical
  let J := patch G ∅
  have one : 1∈types G := mem_image.mpr ⟨f,mem_univ _,rep.one f fm⟩
  have ct := incidences G F rep
  have keep := (matching_profile G bad one rep.one rep.independent).1
  have pos := card_pos.mpr non
  have remaining : (∑v∈F.erase f,nbr J v (rich G))≤∑_v∈F.erase f,2 :=
    sum_le_sum (fun v m => available G rep v (mem_of_mem_erase m))
  simp only [sum_const,Nat.nsmul_eq_mul] at remaining
  have part := sum_erase_add F (fun v => nbr J v (rich G)) fm
  change (∑v∈F.erase f,nbr J v (rich G))+nbr J f (rich G)=(∑v∈F,nbr J v (rich G)) at part
  have num := card_erase_add_one fm
  have limit := available G rep f fm
  change _≤∑v∈F,nbr J v (rich G) at ct
  change nbr J f (rich G)≤2 at limit
  change nbr J f (rich G)=2
  omega

theorem total_loss_even (bad : bound G<gamma G) (non : (exceptional G).Nonempty) :
    ∃k, (∑v∈rich G,loss G v)=2*k := by
  classical
  obtain ⟨F,rep⟩ := exists_representatives G
  refine ⟨F.card,?_⟩
  rw [sum_congr rfl (fun _ vm => loss_eq G rep vm),sum_nbr]
  rw [sum_congr rfl (fun f fm => saturated G bad rep non f fm)]
  simp [Nat.mul_comm]

end Graffiti384b.OddStars.CollisionBudget
#print axioms Graffiti384b.OddStars.CollisionBudget.sum_nbr
#print axioms Graffiti384b.OddStars.CollisionBudget.loss_eq
#print axioms Graffiti384b.OddStars.CollisionBudget.at_most_one
#print axioms Graffiti384b.OddStars.CollisionBudget.saturated
#print axioms Graffiti384b.OddStars.CollisionBudget.total_loss_even
