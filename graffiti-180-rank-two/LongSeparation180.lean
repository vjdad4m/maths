import LongArm180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every nonroot vertical edge on the disagreement forest is a bridge
of the whole alternating graph. -/
theorem vertical_bridge {G : SimpleGraph V} {r t s : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (rt : r≠t) (rs : r≠s) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    t∈D → s∈D → Arc G r t s → ¬(carve G P t s).Reachable t s := by
  classical
  intro P D td sd ts
  let H := alternating G P
  let K := carve G P t s
  obtain ⟨hc,star⟩ := alternating_parity G h.connected r odd
  apply disconnected_ends hc
  intro kc
  change K.Connected at kc
  have keep {i : V} (ri : G.Adj r i) : K.Adj r i := by
    apply deleteEdges_adj.mpr
    refine ⟨star i ri,?_⟩
    intro pair
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair) with a|a
    · exact rt a.1
    · exact rs a.1
  obtain ⟨i,j,ei,ej,ij⟩ := block_neighbors G h.connected h.order h.block r
  obtain ⟨F,fk,ft⟩ := kc.exists_isTree_le
  obtain ⟨M,mk,tree,full,_⟩ := full_star_exchange K F fk ft (by have := h.order; omega) r
  have internal : r∉leaves M := fun l => ij (leaf_unique M l (full i (keep ei)) (full j (keep ej)))
  have mh : M≤H := mk.trans (H.deleteEdges_le _)
  have forced := forced_vertical h tree mh internal td sd (vertical_adj ts.1 ts.2.1 odd)
  exact (deleteEdges_adj.mp (show K.Adj t s from mk forced)).2 (Set.mem_singleton_iff.mpr rfl)

/-- The positive-depth vertices on a longest arm form a spine, with the
first neighbor as its initial vertex. -/
theorem route_spine {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) {m : ℕ} {f : ℕ→V} (long : 2≤m) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    let C := D.filter (fun v => 0<G.dist v r ∧ v=f (G.dist v r))
    (∀ v∈D,G.dist v r≤m) → (∀ k≤m,f k∈D ∧ G.dist (f k) r=k) →
      (∀ k<m,Arc G r (f k) (f (k+1))) →
      Spine G r C (f 1) ∧ f 2∈C := by
  classical
  intro P D C high data arcs
  have hit {k : ℕ} (pos : 0<k) (cap : k≤m) : f k∈C := by
    obtain ⟨fd,df⟩ := data k cap
    exact mem_filter.mpr ⟨fd,by simp only [df,pos,and_self]⟩
  have df1 := (data 1 (by omega)).2
  have df2 := (data 2 long).2
  have cm1 := hit (k:=1) (by omega) (by omega)
  have cm2 := hit (k:=2) (by omega) long
  refine ⟨⟨?_,cm1,?_,?_,?_,?_,⟨f 2,mem_erase.mpr ⟨?_,cm2⟩⟩⟩,cm2⟩
  · intro rc
    have pos := (mem_filter.mp rc).2.1
    rw [dist_self] at pos
    omega
  · intro v vm
    rw [df1]
    exact (mem_filter.mp vm).2.1
  · intro v vm z zm eq
    exact (mem_filter.mp vm).2.2.trans ((congrArg f eq).trans (mem_filter.mp zm).2.2.symm)
  · intro i im it
    obtain ⟨id,pos,eq⟩ := mem_filter.mp im
    let k := G.dist i r-1
    have cap := high i id
    have dk : k+1=G.dist i r := by dsimp [k]; omega
    have kp : 0<k := by
      apply Nat.pos_of_ne_zero
      intro zero
      have one : G.dist i r=1 := by omega
      exact it (eq.trans (congrArg f one))
    refine ⟨f k,hit kp (by omega),?_⟩
    have ix : f (k+1)=i := (congrArg f dk).trans eq.symm
    exact ix ▸ arcs k (by omega)
  · intro v vm i j vi vj di dj
    have pos := (mem_filter.mp vm).2.1
    have vr : v≠r := by intro e; rw [e,dist_self] at pos; omega
    exact h.outward (mem_sdiff.mp (mem_filter.mp vm).1).1 vr vi vj di dj
  · intro eq
    have := congrArg (fun z => G.dist z r) eq
    change G.dist (f 2) r=G.dist (f 1) r at this
    omega

#print axioms vertical_bridge
#print axioms route_spine
end Minimal180.RootEar
