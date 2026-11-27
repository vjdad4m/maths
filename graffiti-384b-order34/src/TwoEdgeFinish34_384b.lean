import Triangle34_384b
import TwoEdgeExact34_384b

namespace Graffiti384b.TwoEdge34
open Finset SimpleGraph CliqueChoice LowSample
open private LowSample.anchors LowSample.two_degree from LowSample384b
open private FiniteRange.bad from FiniteRange384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the two-disjoint-edge anchor graph the very same endpoint has a
private ear triangle, no four-clique, and a matching link of known order. -/
theorem same_endpoint (res : Minimal.Residual G) (n : Fintype.card V=34) {y z : V}
    (yt : y∈twos G) (zt : z∈twos G) (yz : y≠z)
    (nocross : ∀ a∈G.neighborFinset y,∀ b∈G.neighborFinset z,¬G.Adj a b) :
    let W := (twos G).biUnion (G.neighborFinset ·)
    ∃ e∈({y,z} : Finset V),∃ w∈W,∃ b∈W,G.neighborFinset e={w,b} ∧ G.Adj w b ∧
      G.neighborFinset w∩G.neighborFinset b={e} ∧ (∀ K : Finset V,G.IsNClique 4 K → w∉K) ∧
      (∀ x∈ForkGuard34.candidates G W,¬G.Adj w x) ∧
      (∀ x∈G.neighborFinset w,nbr G x (G.neighborFinset w)≤1) ∧
      G.degree w=2*trianglesAt G w + (if ∃ x∈G.neighborFinset w,trianglesAt G x=0 then 1 else 0) := by
  classical
  have pos := (Frontier34.ears G res n).2.1
  obtain ⟨_,_,ears,_,_⟩ := SharedExact34.failure_profile G (Frontier34.boundary G res n).2.1 yz
    (LowSample.two_degree G yt) (LowSample.two_degree G zt) (by have := pos y yt; omega) (by have := pos z zt; omega) res.2.2.1
  obtain ⟨w,ww,_,no4,blind,small⟩ := Triangle34.scored_anchor G res n
  obtain ⟨e,ec,b,bw,ear,wb,ew,eb,priv,thin⟩ := at_endpoint G ears (fun v vt => by have := pos v vt; omega)
    (Triangle34.disjoint G res n yt zt yz).1 nocross ww blind small
  have wp := (TrianglePrune.triangle_iff G w).mpr ⟨e,b,ew.symm,wb,eb⟩
  exact ⟨e,ec,w,ww,b,bw,ear,wb,priv,no4,blind,thin,degree_formula G res.2.2.2.1 wp thin⟩

/-- In every normalized order-34 failure with two ears, the two anchor
edges are vertex-disjoint and at least one edge joins their endpoints. -/
theorem cross_required (res : Minimal.Residual G) (n : Fintype.card V=34) {y z : V}
    (yt : y∈twos G) (zt : z∈twos G) (yz : y≠z) :
    Disjoint (G.neighborFinset y) (G.neighborFinset z) ∧
    ∃ a∈G.neighborFinset y,∃ c∈G.neighborFinset z,G.Adj a c := by
  have apart := (Triangle34.disjoint G res n yt zt yz).1
  refine ⟨apart,?_⟩
  by_contra! none
  have pos := (Frontier34.ears G res n).2.1
  exact (not_lt_of_ge (exact G n (Frontier34.boundary G res n).2.1 yz (LowSample.two_degree G yt) (LowSample.two_degree G zt)
    (by have := pos y yt; omega) (by have := pos z zt; omega) none)) res.2.2.1

/-- All cross edges on the four distinct anchors meet b, and at least one
such edge occurs. The private endpoint a has no cross edge. -/
theorem remaining (res : Minimal.Residual G) (n : Fintype.card V=34) {y z : V}
    (yt : y∈twos G) (zt : z∈twos G) (yz : y≠z) :
    ∃ e f a b,((e=y ∧ f=z) ∨ (e=z ∧ f=y)) ∧
      Disjoint (G.neighborFinset e) (G.neighborFinset f) ∧
      G.neighborFinset e={a,b} ∧ G.Adj a b ∧ G.neighborFinset a∩G.neighborFinset b={e} ∧
      (∀ i∈G.neighborFinset f,¬G.Adj a i) ∧ (∃ i∈G.neighborFinset f,G.Adj b i) := by
  have pos := (Frontier34.ears G res n).2.1
  obtain ⟨e,f,a,b,which,ear,ab,priv,miss⟩ := Triangle34.end_anchor G n (Frontier34.boundary G res n).2.1 yz
    (LowSample.two_degree G yt) (LowSample.two_degree G zt) (by have := pos y yt; omega) (by have := pos z zt; omega) res.2.2.1
  obtain ⟨et,ft,ef⟩ : e∈twos G ∧ f∈twos G ∧ e≠f := by
    rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨yt,zt,yz⟩
    · exact ⟨zt,yt,yz.symm⟩
  obtain ⟨dis,i,ie,j,jf,ij⟩ := cross_required G res n et ft ef
  refine ⟨e,f,a,b,which,dis,ear,ab,priv,miss,j,jf,?_⟩
  rw [ear,mem_insert,mem_singleton] at ie
  rcases ie with rfl|rfl
  · exact (miss j jf ij).elim
  · exact ij

end Graffiti384b.TwoEdge34
#print axioms Graffiti384b.TwoEdge34.same_endpoint
#print axioms Graffiti384b.TwoEdge34.cross_required
#print axioms Graffiti384b.TwoEdge34.remaining

