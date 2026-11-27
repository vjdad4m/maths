import SharedExact34_384b
import TwoEdgeLink34_384b
import TwoEdgeFrame34_384b

namespace Graffiti384b.TwoEdge34
open Finset SimpleGraph CliqueChoice LowSample
open private LowSample.anchors LowSample.two_degree from LowSample384b
open private FiniteRange.bad from FiniteRange384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem at_endpoint {y z w : V} (ears : twos G={y,z})
    (pos : ∀ e∈twos G,0<trianglesAt G e) (sep : Disjoint (G.neighborFinset y) (G.neighborFinset z))
    (nocross : ∀ a∈G.neighborFinset y,∀ b∈G.neighborFinset z,¬G.Adj a b)
    (ww : w∈(twos G).biUnion (G.neighborFinset ·))
    (blind : ∀ x∈ForkGuard34.candidates G ((twos G).biUnion (G.neighborFinset ·)),¬G.Adj w x)
    (small : ∀ x∈ForkGuard34.row G ((twos G).biUnion (G.neighborFinset ·)) w,
      nbr G x (ForkGuard34.row G ((twos G).biUnion (G.neighborFinset ·)) w)≤1) :
    let W := (twos G).biUnion (G.neighborFinset ·)
    ∃ e∈({y,z} : Finset V),∃ b∈W,G.neighborFinset e={w,b} ∧ G.Adj w b ∧
      G.Adj e w ∧ G.Adj e b ∧ G.neighborFinset w∩G.neighborFinset b={e} ∧
      (∀ x∈G.neighborFinset w,nbr G x (G.neighborFinset w)≤1) := by
  let W := (twos G).biUnion (G.neighborFinset ·)
  obtain ⟨e,et,we⟩ := mem_biUnion.mp ww
  have ew := (G.mem_neighborFinset _ _).mp we
  have only (v : V) (vt : v∈twos G) (wv : G.Adj w v) : v=e := by
    by_contra ne
    have ec := (show e∈({y,z} : Finset V) from ears ▸ et)
    have vc := (show v∈({y,z} : Finset V) from ears ▸ vt)
    have vm := (G.mem_neighborFinset _ _).mpr wv.symm
    simp only [mem_insert,mem_singleton] at ec vc
    rcases ec with ey|ez <;> rcases vc with vy|vz
    · exact ne (vy.trans ey.symm)
    · exact disjoint_left.mp sep (ey ▸ we) (vz ▸ vm)
    · exact disjoint_left.mp sep (vy ▸ vm) (ez ▸ we)
    · exact ne (vz.trans ez.symm)
  have ec : e∈({y,z} : Finset V) := ears ▸ et
  have all (v : V) (vt : v∈twos G) : G.neighborFinset v⊆W := fun _ m => mem_biUnion.mpr ⟨v,vt,m⟩
  obtain ⟨i,j,eq,ei,ej,ij⟩ := SharedExact34.ear_pair G (LowSample.two_degree G et) (pos e et)
  have pair : ∃ b∈W,G.neighborFinset e={w,b} ∧ G.Adj w b ∧ G.Adj e b := by
    rw [eq,mem_insert,mem_singleton] at we
    rcases we with rfl|rfl
    · exact ⟨j,all e et ((G.mem_neighborFinset _ _).mpr ej),eq,ij,ej⟩
    · exact ⟨i,all e et ((G.mem_neighborFinset _ _).mpr ei),eq.trans (pair_comm ..),ij.symm,ei⟩
  obtain ⟨b,bw,ear,wb,eb⟩ := pair
  have inside (x : V) (xw : x∈W) (wx : G.Adj w x) : x=b := by
    obtain ⟨f,ft,xf⟩ := mem_biUnion.mp xw
    by_cases fe : f=e
    · rw [fe,ear,mem_insert,mem_singleton] at xf
      exact xf.resolve_left wx.ne.symm
    have fc : f∈({y,z} : Finset V) := ears ▸ ft
    simp only [mem_insert,mem_singleton] at ec fc
    rcases ec with ey|ez <;> rcases fc with fy|fz
    · exact (fe (fy.trans ey.symm)).elim
    · exact (nocross w (ey ▸ we) x (fz ▸ xf) wx).elim
    · exact (nocross x (fy ▸ xf) w (ez ▸ we) wx.symm).elim
    · exact (fe (fz.trans ez.symm)).elim
  obtain ⟨priv,thin⟩ := link G ww bw wb ew eb ear inside only blind small
  exact ⟨e,ec,b,bw,ear,wb,ew,eb,priv,thin⟩

/-- The catalogue inequality itself for graphs of order 34 and diversity 33
with two distinct triangular ears and no edge between their anchor pairs. -/
theorem exact (n : Fintype.card V=34) (t : (types G).card=33) {y z : V} (yz : y≠z)
    (dy : G.degree y=2) (dz : G.degree z=2) (py : 0<trianglesAt G y) (pz : 0<trianglesAt G z)
    (nocross : ∀ a∈G.neighborFinset y,∀ b∈G.neighborFinset z,¬G.Adj a b) :
    gamma G≤bound G := by
  classical
  by_contra! fail
  obtain ⟨q,h,ears,_,hi⟩ := SharedExact34.failure_profile G t yz dy dz py pz fail
  have sep := SharedExact34.separate G n t yz dy dz py pz fail
  have yt : y∈twos G := ears ▸ mem_insert_self .. 
  have zt : z∈twos G := ears ▸ mem_insert_of_mem (mem_singleton_self _)
  let W := (twos G).biUnion (G.neighborFinset ·)
  have wh : W⊆high G := by
    intro w wm
    obtain ⟨e,et,em⟩ := mem_biUnion.mp wm
    rw [ears,mem_insert,mem_singleton] at et
    exact hi (et.elim (fun val => mem_union_left _ (val ▸ em)) (fun val => mem_union_right _ (val ▸ em)))
  have all (v : V) (vt : v∈twos G) : G.neighborFinset v⊆W := fun _ m => mem_biUnion.mpr ⟨v,vt,m⟩
  have anchor (w : V) (wm : w∈W) : ∃ e∈twos G,G.Adj w e := by
    obtain ⟨e,et,em⟩ := mem_biUnion.mp wm
    exact ⟨e,et,((G.mem_neighborFinset _ _).mp em).symm⟩
  have pos (e : V) (et : e∈twos G) : 0<trianglesAt G e := by
    rw [ears,mem_insert,mem_singleton] at et
    exact et.elim (fun val => val ▸ py) (fun val => val ▸ pz)
  obtain ⟨w,ww,blind,small⟩ := ForkGuard34.matching G wh all anchor (by omega) fail
  obtain ⟨e,ec,b,_,ear,wb,_,_,priv,thin⟩ := at_endpoint G ears pos sep nocross ww blind small
  have score := half_degree G thin
  rcases mem_insert.mp ec with ey|m
  · subst e
    exact (not_lt_of_ge (finish_frame G n t h yt zt yz hi sep nocross ear wb priv score)) fail
  · obtain rfl := mem_singleton.mp m
    exact (not_lt_of_ge (finish_frame G n t h zt yt yz.symm (by rw [union_comm]; exact hi) sep.symm
      (fun a az c cy ac => nocross c cy a az ac.symm) ear wb priv score)) fail

end Graffiti384b.TwoEdge34
#print axioms Graffiti384b.TwoEdge34.at_endpoint
#print axioms Graffiti384b.TwoEdge34.exact
