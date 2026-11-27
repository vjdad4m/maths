import SecondEdge180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem xor_diff (a b x y : Prop) [Decidable a] [Decidable b] [Decidable x] [Decidable y]
    (law : (a ↔ b) ↔ ¬(x ↔ y)) :
    xor (decide a) (decide x) ≠ xor (decide b) (decide y) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hx : x <;> by_cases hy : y <;> simp_all

/-- Flip the parity coloring across the second bridge after erasing the
first neighbor. No horizontal edge can have the root as either endpoint. -/
theorem arm_color (J : SimpleGraph V) (jc : J.Connected) (r : V) (odd : Bool) (A : Finset V)
    (ai : Indep J A) (t s : V) :
    let P := parity J r odd
    let D := (A∪P)\(A∩P)
    Spine J r (D.erase r) t → s∈D.erase r → Arc J r t s → ¬(carve J P t s).Reachable t s →
      Indep J (univ\(A∪P)) → TwoColor J (univ.erase t) := by
  classical
  intro P D sp sd ts broken outside
  let K := carve J P t s
  let R (v : V) := K.Reachable r v
  let c (v : V) := xor (decide (v∈P)) (decide (R v))
  have layers := separated_layers jc sp sd ts odd broken
  have flat {a b : V} (e : J.Adj a b) (same : a∈P ↔ b∈P) : J.dist a r=J.dist b r := by
    have l := jc.dist_triangle (u:=a) (v:=b) (w:=r)
    have m := jc.dist_triangle (u:=b) (v:=a) (w:=r)
    rw [dist_eq_one_iff_adj.mpr e] at l
    rw [dist_eq_one_iff_adj.mpr e.symm] at m
    change a∈parity J r odd ↔ b∈parity J r odd at same
    simp only [mem_parity] at same
    cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] at same <;> omega
  have meets {a b : V} (e : J.Adj a b) (same : a∈P ↔ b∈P) : a∈D ∨ b∈D := by
    by_contra! neither
    have flip {v : V} (no : v∉D) : v∈A ↔ v∈P := by
      change v∉(A∪P)\(A∩P) at no
      simp only [mem_sdiff,mem_union,mem_inter] at no
      tauto
    by_cases ap : a∈P
    · exact ai a ((flip neither.1).mpr ap) b ((flip neither.2).mpr (same.mp ap)) e.ne e
    · have absent {v : V} (no : v∉D) (np : v∉P) : v∈univ\(A∪P) :=
        mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim (fun va => np ((flip no).mp va)) np⟩
      exact outside a (absent neither.1 ap) b (absent neither.2 (fun bp => ap (same.mpr bp))) e.ne e
  have notRoot {a b : V} (e : J.Adj a b) (eq : J.dist a r=J.dist b r) : a≠r := by
    intro ar
    have db := dist_eq_one_iff_adj.mpr (ar ▸ e.symm : J.Adj b r)
    rw [ar,dist_self,db] at eq
    omega
  apply (color_function J _).mpr
  refine ⟨c,?_⟩
  intro a ha b hb e
  have atip := (mem_erase.mp ha).1
  have btip := (mem_erase.mp hb).1
  by_cases same : a∈P ↔ b∈P
  · have eq := flat e same
    have diff : ¬(R a ↔ R b) := by
      rcases meets e same with ad|bd
      · obtain ⟨ar,br⟩ := layers a (mem_erase.mpr ⟨notRoot e eq,ad⟩) atip
        exact fun iff => ar (iff.mpr (br b e.ne.symm eq.symm))
      · obtain ⟨br,ar⟩ := layers b (mem_erase.mpr ⟨notRoot e.symm eq.symm,bd⟩) btip
        exact fun iff => br (iff.mp (ar a e.ne eq))
    exact xor_diff _ _ _ _ ⟨fun _ => diff,fun _ => same⟩
  · have op : a∈P ↔ b∉P := by tauto
    have inK : K.Adj a b := by
      apply deleteEdges_adj.mpr
      refine ⟨⟨e,op⟩,?_⟩
      intro pair
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair) with h|h
      · exact atip h.1
      · exact btip h.2
    have eqR : R a ↔ R b := ⟨fun h => h.trans inK.reachable,fun h => h.trans inK.symm.reachable⟩
    exact xor_diff _ _ _ _ ⟨fun h => (same h).elim,fun n => (n eqR).elim⟩


/-- Both neighbors of the root must themselves be singly marked in any
failed rank-two block. In particular an even-parity-only root must have
two neighbors in the independent set. -/
theorem both_ports {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) {w : V} (rw : G.Adj r w) :
    let P := parity G r odd
    w∈(A∪P)\(A∩P) := by
  classical
  intro P
  apply Classical.byContradiction
  intro out
  obtain ⟨_,t,rt,sp⟩ := single_arm h rw out
  obtain ⟨s,sd,ts⟩ := sp.first_step
  exact erase_odd h t (arm_color G h.connected r odd A h.independent t s sp sd ts
    (second_bridge h rt sp sd ts) (arm_outside h rw out))

/-- Exact bipartization-deficit-two upper bound whenever the root has a
neighbor outside the symmetric difference of the two marks. -/
theorem outside_port (G : SimpleGraph V) (gc : G.Connected) (block : NoCut G)
    (order : 2<Fintype.card V) (rank : Fintype.card V≤bipartiteNum G+2)
    (r : V) (odd : Bool) (A : Finset V) (ind : Indep G A) :
    let P := parity G r odd
    (∃ w, G.Adj r w ∧ w∉(A∪P)\(A∩P)) →
      1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  classical
  rintro P ⟨w,rw,out⟩
  by_contra! bad
  exact out (both_ports (show FailedTwo G r odd A from ⟨gc,block,order,rank,ind,bad⟩) rw)

#print axioms arm_color
#print axioms both_ports
#print axioms outside_port
end Minimal180.RootEar
