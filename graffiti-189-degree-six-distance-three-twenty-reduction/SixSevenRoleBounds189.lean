import SixSevenCross189
namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open scoped BigOperators
open private Shore shore_off from AdjacentCutFiveActual189
open private Cmp from SixCutFar189
open private no_common_far from SixDistanceThreeShort189
open private d2 from CrossSaturation189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

def allowedRoles (i : Fin 8) : Finset (Fin 8) :=
  match i.val with
  | 0 => {0,1,4,6}
  | 1 => {0,1,3,4,6}
  | 2 => {2,3,5,6}
  | 3 => {1,2,3,5,6}
  | 4 => {0,1,4,5,6,7}
  | 5 => {2,3,4,5,6,7}
  | 6 => {0,1,2,3,4,5,6,7}
  | _ => {4,5,6,7}

theorem six_role_of_edge (hc : G.Connected) (far : 3≤G.dist a b)
    {x y : V} (xa : x≠a) (xb : x≠b) (ya : y≠a) (yb : y≠b)
    (xy : G.Adj x y) {i j : Fin 8} (hx : sixClassSpec G a b x i)
    (hy : sixClassSpec G a b y j) : j∈allowedRoles i := by
  have xn : ¬(G.Adj a x ∧ G.Adj b x) := no_common_far far
  have yn : ¬(G.Adj a y ∧ G.Adj b y) := no_common_far far
  have visAX (p : G.Adj a y) (q : ¬G.Adj a x) : G.dist a x=2 := by
    simpa [DistanceTwo] using d2 hc xa.symm q p xy.symm
  have visBX (p : G.Adj b y) (q : ¬G.Adj b x) : G.dist b x=2 := by
    simpa [DistanceTwo] using d2 hc xb.symm q p xy.symm
  have visAY (p : G.Adj a x) (q : ¬G.Adj a y) : G.dist a y=2 := by
    simpa [DistanceTwo] using d2 hc ya.symm q p xy
  have visBY (p : G.Adj b x) (q : ¬G.Adj b y) : G.dist b y=2 := by
    simpa [DistanceTwo] using d2 hc yb.symm q p xy
  fin_cases i <;> fin_cases j
  all_goals try decide
  all_goals simp only [sixClassSpec] at hx hy
  all_goals exfalso; tauto

noncomputable def allowedInShore (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (D : Finset V) (i : Fin 8) : Finset V :=
  (allowedRoles i).biUnion (sixBucket G a b D)

theorem allowedInShore_card {D : Finset V} (i : Fin 8) :
    (allowedInShore G a b D i).card = ∑ j ∈ allowedRoles i, (sixBucket G a b D j).card := by
  classical
  unfold allowedInShore
  exact card_biUnion (fun _ _ _ _ ij=>sixBuckets_disjoint a b D D ij)

theorem role_card_bound (hc : G.Connected) (far : 3≤G.dist a b) {C : Cmp G a b}
    {u : V} {i : Fin 8} (uc : u∈Shore C) (h : sixClassSpec G a b u i) :
    (inside G (Shore C) u).card+1≤(allowedInShore G a b (Shore C) i).card := by
  classical
  let T := allowedInShore G a b (Shore C) i
  have un : ¬(G.Adj a u ∧ G.Adj b u) := no_common_far far
  have uu : i∈allowedRoles i := by fin_cases i <;> decide
  have ut : u∈T := mem_biUnion.mpr ⟨i,uu,(mem_sixBucket un i).mpr ⟨uc,h⟩⟩
  have hu : insert u (inside G (Shore C) u)⊆T := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zi
    · exact ut
    obtain ⟨zc,uz⟩ := mem_filter.mp zi
    let j := sixClass G a b z
    have zn : ¬(G.Adj a z ∧ G.Adj b z) := no_common_far far
    have zh := (class_spec zn j).mp (show sixClass G a b z=j from rfl)
    have ua : u≠a := fun e=>(shore_off C).1 (e ▸ uc)
    have ub : u≠b := fun e=>(shore_off C).2 (e ▸ uc)
    have za : z≠a := fun e=>(shore_off C).1 (e ▸ zc)
    have zb : z≠b := fun e=>(shore_off C).2 (e ▸ zc)
    have al := six_role_of_edge hc far ua ub za zb uz h zh
    exact mem_biUnion.mpr ⟨j,al,(mem_sixBucket zn j).mpr ⟨zc,zh⟩⟩
  have c := card_le_card hu
  rw [card_insert_of_not_mem (show u∉inside G (Shore C) u by simp [inside])] at c
  exact c

#print axioms role_card_bound
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
