import PosaRouteCut189
open SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaOrderedPair
set_option warningAsError true
namespace Graffiti189LongestPath.PosaSpliceCommon
variable {V : Type*} {G : SimpleGraph V}

theorem ordered_append_mid {a b u v w : V} (p : G.Walk a b) {i j k : Nat}
    {q : G.Walk u v} {r : G.Walk v w} (mid : v=p.getVert j)
    (qp : q.IsPath) (qo : Ordered p q) (ro : Ordered p r)
    (qb : Bounds p q i j) (rb : Bounds p r j k) :
    Ordered p (q.append r) := by
  intro s t sl tl st u' v' ul vl e f
  rw [length_append] at sl tl
  rw [getVert_append] at e f
  by_cases tQ : t<q.length
  · have sQ : s<q.length := by omega
    rw [if_pos sQ] at e
    rw [if_pos tQ] at f
    exact qo s t (by omega) (by omega) st u' v' ul vl e f
  rw [if_neg tQ] at f
  by_cases sQ : s<q.length
  · rw [if_pos sQ] at e
    have uQ := (qb u' ul (e ▸ q.getVert_mem_support s)).2
    have vR := (rb v' vl (f ▸ r.getVert_mem_support (t-q.length))).1
    have ne : u'≠j := by
      intro h
      have endq : q.getVert s=q.getVert q.length := e.trans
        (by rw [h,getVert_length]; exact mid.symm)
      have eq := qp.getVert_injOn (Nat.le_of_lt sQ) (by simp) endq
      omega
    omega
  rw [if_neg sQ] at e
  exact ro (s-q.length) (t-q.length) (by omega) (by omega) (by omega) u' v' ul vl e f

def Hits {a b : V} {p : G.Walk a b} (P : OrderedPair p) (i : Nat) : Prop :=
  p.getVert i∈P.left.support ∨ p.getVert i∈P.right.support

def OrderedPair.swap {a b : V} {p : G.Walk a b} (P : OrderedPair p) : OrderedPair p :=
  ⟨P.right,P.left,P.rightPath,P.leftPath,P.rightOrder,P.leftOrder,
    fun z zr zl => P.only z zl zr,
    (by
      obtain ⟨x,h,lo,hi⟩ := P.internal_exact
      exact ⟨x,h.elim Or.inr Or.inl,lo,hi⟩)⟩

theorem internal_index_not_endpoint {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (i : Nat) (lo : 0<i) (hi : i<p.length) : p.getVert i≠a ∧ p.getVert i≠b := by
  constructor
  · intro e
    have h := hp.getVert_injOn hi.le (by change 0≤p.length; omega) (e.trans p.getVert_zero.symm)
    omega
  · intro e
    have h := hp.getVert_injOn hi.le (by simp) (e.trans p.getVert_length.symm)
    omega

#print axioms ordered_append_mid
end Graffiti189LongestPath.PosaSpliceCommon
