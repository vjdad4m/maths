import SparseRanks
import SparseSwap
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph JointRank TwoEars
open private Squares29.pair_at from SquareTriple29
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Retain the ear temporarily when its other anchor is absent. Its sampled
cubic neighbor and the endpoint opposite the ear then permit a replacement. -/
private theorem cubic_swap {e v : V} (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) (em : e∈LowSample.twos G) (ev : G.Adj e v)
    (dg : G.degree v=3) (sc : trianglesAt G v=2) : massBound G 3124550 := by
  classical
  let X := high G
  let E := LowSample.twos G
  have ed := LowSample.two_degree G em
  have vm : v∈X := mem_filter.mpr ⟨mem_univ _,dg.ge⟩
  have sep : Disjoint X E := disjoint_left.mpr (fun _ h e => (mem_sdiff.mp e).2 h)
  have unique (a : V) (am : a∈E) (av : G.Adj a v) : a=e := by
    apply Classical.byContradiction; intro ne
    have d := AnchorPairs.disjoint_anchors G t q bad ne (LowSample.two_degree G am) ed
    exact disjoint_left.mp d ((G.mem_neighborFinset ..).mpr av) ((G.mem_neighborFinset ..).mpr ev)
  have free : nbr G v (E.erase e)=0 := card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr (by
    intro a am; obtain ⟨ae,va⟩ := mem_filter.mp am
    exact (mem_erase.mp ae).1 (unique a (mem_erase.mp ae).2 va.symm)))
  obtain ⟨P,guard⟩ := protecting_pair G dg sc
  have sz := guard.1
  have en : e∈G.neighborFinset v := (G.mem_neighborFinset ..).mpr ev.symm
  have ve : v∉P := fun vp => G.not_mem_neighborFinset_self _ (guard.2.1 vp)
  have ep : e∈P := by
    apply Classical.byContradiction; intro off
    have inc : insert v P⊆G.neighborFinset e := insert_subset ((G.mem_neighborFinset ..).mpr ev) (guard.2.2 e en off)
    have ct := card_le_card inc
    rw [card_insert_of_not_mem ve,sz,card_neighborFinset_eq_degree,ed] at ct; omega
  obtain ⟨z,ez,pair⟩ := Squares29.pair_at sz ep
  have zp : z∈P := pair ▸ mem_insert_of_mem (mem_singleton_self _)
  have vz := (G.mem_neighborFinset ..).mp (guard.2.1 zp)
  have count : (G.neighborFinset v\P).card=1 := by rw [card_sdiff guard.2.1,card_neighborFinset_eq_degree,dg,sz]
  obtain ⟨b,bm⟩ := card_pos.mp (show 0<(G.neighborFinset v\P).card by omega)
  obtain ⟨bn,bp⟩ := mem_sdiff.mp bm
  have vb := (G.mem_neighborFinset ..).mp bn
  have eb := ((G.mem_neighborFinset ..).mp (guard.2.2 b bn bp ep)).symm
  have bz := (G.mem_neighborFinset ..).mp (guard.2.2 b bn bp zp)
  have bh := TwoEars.high_anchors G t q bad ed ((G.mem_neighborFinset ..).mpr eb)
  have zh : z∈X := by
    apply Classical.byContradiction; intro low
    have sub : {v,b}⊆G.neighborFinset z := insert_subset ((G.mem_neighborFinset ..).mpr vz.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr bz.symm))
    have lower := card_le_card sub
    rw [card_pair vb.ne,card_neighborFinset_eq_degree] at lower
    have ze : z∈E := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,lower⟩,low⟩
    exact ez (unique z ze vz.symm).symm
  have ind : ∀u∈E,∀i∈E,¬G.Adj u i := by
    intro u um i im ui
    exact (mem_sdiff.mp im).2 (TwoEars.high_anchors G t q bad (LowSample.two_degree G um) ((G.mem_neighborFinset ..).mpr ui))
  obtain ⟨hs,_⟩ := TwoEars.profile G t q bad
  obtain ⟨inj,_,_,_⟩ := Repair.maximal_diversity G (by omega)
  rw [bound,t] at bad
  exact swap_mass G X E hs sep ind (fun i h => LowSample.two_degree G h) Subset.rfl inj em vm zh bh
    vb.ne bz.ne.symm vz.ne eb ev sc dg (pair ▸ guard) free (by omega)

/-- A score-two anchor always saves 3,124,550 additional trials, whether it is
cubic and can be replaced or its larger degree already gives the saving. -/
theorem two_score_budget {e v : V} (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) (em : e∈LowSample.twos G) (ev : G.Adj e v) (sc : trianglesAt G v=2) :
    let A := (LowSample.twos G).biUnion (G.neighborFinset ·)
    3124550+(∑ a∈A,credit (rank (high G) (trianglesAt G) a))≤12407000 := by
  classical
  let A := (LowSample.twos G).biUnion (G.neighborFinset ·)
  let r := rank (high G) (trianglesAt G)
  let c := fun a => credit (r a)
  let h := fun a => augmented (r a) (G.degree a)
  have va : v∈A := mem_biUnion.mpr ⟨e,em,(G.mem_neighborFinset ..).mpr ev⟩
  have vh := TwoEars.high_anchors G t q bad (LowSample.two_degree G em) ((G.mem_neighborFinset ..).mpr ev)
  have hs := (TwoEars.profile G t q bad).1
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have low := rank_lower _ _ inj 2 floor vh
  change 2+r v≤trianglesAt G v at low
  have zero : r v=0 := by omega
  have le (a : V) : c a≤h a := credit_le_augmented .. 
  change 3124550+(∑ a∈A,c a)≤12407000
  by_cases cubic : G.degree v=3
  · have tot := rank_account G t q bad 3124550 (cubic_swap G t q bad em ev cubic sc)
    exact (Nat.add_le_add_left (sum_le_sum (fun a _ => le a)) 3124550).trans tot
  · have big := (mem_filter.mp vh).2
    have vc : c v+3124550≤h v := by
      simp [h,c,augmented,zero,show 4≤G.degree v by omega]
    have tot := rank_account G t q bad 0 (base_mass G t q bad)
    change 0+(∑ a∈A,h a)≤12407000 at tot
    have rem := sum_le_sum (s:=A.erase v) (fun a _ => le a)
    have add1 := sum_erase_add A h va
    have add2 := sum_erase_add A c va
    omega
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.two_score_budget
