import LongSeparation180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem xor_diff (a b x y : Prop) [Decidable a] [Decidable b] [Decidable x] [Decidable y]
    (law : (a ↔ b) ↔ ¬(x ↔ y)) :
    xor (decide a) (decide x) ≠ xor (decide b) (decide y) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hx : x <;> by_cases hy : y <;> simp_all

/-- A spine meeting every horizontal edge yields a one-vertex odd-cycle
transversal when its first edge separates the alternating graph. -/
theorem covering_spine_color (J : SimpleGraph V) (jc : J.Connected) (r : V) (odd : Bool)
    (C : Finset V) (t s : V) :
    let P := parity J r odd
    Spine J r C t → s∈C → Arc J r t s → ¬(carve J P t s).Reachable t s →
    (∀ {a b}, J.Adj a b → (a∈P ↔ b∈P) → a∈C ∨ b∈C) → TwoColor J (univ.erase t) := by
  classical
  intro P sp sd ts broken meets
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
  apply (color_function J _).mpr
  refine ⟨c,?_⟩
  intro a ha b hb e
  have atip := (mem_erase.mp ha).1
  have btip := (mem_erase.mp hb).1
  by_cases same : a∈P ↔ b∈P
  · have eq := flat e same
    have diff : ¬(R a ↔ R b) := by
      rcases meets e same with ad|bd
      · obtain ⟨ar,br⟩ := layers a ad atip
        exact fun iff => ar (iff.mpr (br b e.ne.symm eq.symm))
      · obtain ⟨br,ar⟩ := layers b bd btip
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



/-- A hypothetical failed rank-two marking admits a one-vertex odd-cycle
transversal, contradicting the checked deficit-one theorem. -/
theorem no_failed_two {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V} :
    ¬FailedTwo G r odd A := by
  classical
  intro h
  let P := parity G r odd
  let D := (A∪P)\(A∩P)
  obtain ⟨m,f,pos,high,data,arcs⟩ := long_route h
  let t := f 1
  have hit {a b : V} (e : G.Adj a b) (same : a∈P ↔ b∈P) :=
    flat_hits h high data e same
  apply erase_odd h t
  by_cases long : 2≤m
  · let C := D.filter (fun v => 0<G.dist v r ∧ v=f (G.dist v r))
    obtain ⟨sp,sd⟩ := route_spine h long high data arcs
    change Spine G r C t at sp
    have ts := arcs 1 (by omega)
    have rt : r≠t := fun eq => sp.root (eq ▸ sp.tip)
    have rs : r≠f 2 := fun eq => sp.root (eq ▸ sd)
    have broken := vertical_bridge h rt rs (data 1 (by omega)).1 (data 2 long).1 ts
    apply covering_spine_color G h.connected r odd C t (f 2) sp sd ts broken
    intro a b e same
    obtain ⟨k,kp,km,_,which⟩ := hit e same
    obtain ⟨fd,df⟩ := data k km
    have fk : f k∈C := mem_filter.mpr ⟨fd,by simp only [df,kp,and_self]⟩
    exact which.elim (fun eq => Or.inl (eq ▸ fk)) (fun eq => Or.inr (eq ▸ fk))
  · apply (color_function G _).mpr
    refine ⟨fun x => decide (x∈P),?_⟩
    intro a am b bm e eq
    have same : a∈P ↔ b∈P := by
      by_cases ap : a∈P <;> by_cases bp : b∈P <;> simp_all
    obtain ⟨k,kp,km,_,which⟩ := hit e same
    have one : k=1 := by omega
    rw [one] at which
    exact which.elim (mem_erase.mp am).1 (mem_erase.mp bm).1

/-- The full rooted weighted block inequality for every biconnected graph
at bipartization deficit at most two, every root, both parity choices and
every independent mark. -/
theorem rank_two_block (G : SimpleGraph V) (gc : G.Connected) (block : NoCut G)
    (order : 2<Fintype.card V) (rank : Fintype.card V≤bipartiteNum G+2)
    (r : V) (odd : Bool) : localBound G r (parity G r odd) := by
  intro A ind
  by_contra! bad
  exact no_failed_two (show FailedTwo G r odd A from ⟨gc,block,order,rank,ind,bad⟩)

#print axioms covering_spine_color
#print axioms no_failed_two
#print axioms rank_two_block
end Minimal180.RootEar
