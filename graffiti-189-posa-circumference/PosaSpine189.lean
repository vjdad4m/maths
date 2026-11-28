import CycleTwoCuts189
open SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.CycleTwoCuts
set_option warningAsError true
set_option maxHeartbeats 2400000
namespace Graffiti189LongestPath.PosaSpine

variable {V : Type*} {G : SimpleGraph V}

/-- A route visits all spine vertices present in its support in strictly
increasing spine order. Both routes in Pósa's argument have this property. -/
def Ordered {a b u v : V} (p : G.Walk a b) (q : G.Walk u v) : Prop :=
  ∀ s t : Nat, s≤q.length → t≤q.length → s<t →
    ∀ i j : Nat, i≤p.length → j≤p.length →
      q.getVert s=p.getVert i → q.getVert t=p.getVert j → i<j

def Bounds {a b u v : V} (p : G.Walk a b) (q : G.Walk u v) (lo hi : Nat) : Prop :=
  ∀ i≤p.length,p.getVert i∈q.support → lo≤i ∧ i≤hi

theorem ordered_append {a b : V} (p : G.Walk a b) {i j k : Nat}
    {q : G.Walk (p.getVert i) (p.getVert j)} {r : G.Walk (p.getVert j) (p.getVert k)}
    (qp : q.IsPath) (qo : Ordered p q) (ro : Ordered p r)
    (qb : Bounds p q i j) (rb : Bounds p r j k) :
    Ordered p (q.append r) := by
  intro s t sl tl st u v ul vl e f
  rw [length_append] at sl tl
  rw [getVert_append] at e f
  by_cases tQ : t<q.length
  · have sQ : s<q.length := by omega
    rw [if_pos sQ] at e
    rw [if_pos tQ] at f
    exact qo s t (by omega) (by omega) st u v ul vl e f
  rw [if_neg tQ] at f
  by_cases sQ : s<q.length
  · rw [if_pos sQ] at e
    have uQ := (qb u ul (e ▸ q.getVert_mem_support s)).2
    have vR := (rb v vl (f ▸ r.getVert_mem_support (t-q.length))).1
    have ne : u≠j := by
      intro h
      have endq : q.getVert s=q.getVert q.length := e.trans
        (by rw [h,getVert_length])
      have eq := qp.getVert_injOn (Nat.le_of_lt sQ) (by simp) endq
      omega
    omega
  rw [if_neg sQ] at e
  exact ro (s-q.length) (t-q.length) (by omega) (by omega) (by omega) u v ul vl e f

theorem bound_append {a b u v w : V} (p : G.Walk a b)
    {q : G.Walk u v} {r : G.Walk v w} {i j k : Nat} (ij : i≤j) (jk : j≤k)
    (qb : Bounds p q i j) (rb : Bounds p r j k) : Bounds p (q.append r) i k := by
  intro s sl hs
  rw [support_append,List.mem_append] at hs
  exact hs.elim (fun h => ⟨(qb s sl h).1,(qb s sl h).2.trans jk⟩)
    (fun h => ⟨ij.trans (rb s sl (List.mem_of_mem_tail h)).1,
      (rb s sl (List.mem_of_mem_tail h)).2⟩)

theorem ordered_exterior {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    {i j : Nat} (ij : i<j) (jN : j≤p.length)
    {q : G.Walk (p.getVert i) (p.getVert j)} (qp : q.IsPath)
    (only : ∀ z∈q.support,z∈p.support → z=p.getVert i ∨ z=p.getVert j) :
    Ordered p q ∧ Bounds p q i j := by
  have iN := ij.le.trans jN
  have endpoint (k : Nat) (kN : k≤p.length) (kq : p.getVert k∈q.support) : k=i ∨ k=j := by
    rcases only _ kq (p.getVert_mem_support k) with h|h
    · exact Or.inl (hp.getVert_injOn kN iN h)
    · exact Or.inr (hp.getVert_injOn kN jN h)
  constructor
  · intro s t sl tl st u v ul vl e f
    have s' := endpoint u ul (e ▸ q.getVert_mem_support s)
    have t' := endpoint v vl (f ▸ q.getVert_mem_support t)
    have ne1 : u≠j := by
      intro h
      have eq := qp.getVert_injOn sl (le_refl q.length) (e.trans (by rw [h,getVert_length]))
      omega
    have ne2 : v≠i := by
      intro h
      have eq := qp.getVert_injOn tl (Nat.zero_le _) (f.trans (by rw [h,getVert_zero]))
      omega
    rw [s'.resolve_right ne1,t'.resolve_left ne2]
    exact ij
  · intro k kn ks
    rcases endpoint k kn ks with rfl|rfl
    · exact ⟨le_rfl,ij.le⟩
    · exact ⟨ij.le,le_rfl⟩

variable [DecidableEq V]

/-- An arbitrary spine interval, with exact index membership, expressed as
a simple walk so that it can be appended to exterior detours. -/
theorem spine_segment {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (i j : Nat) (ij : i≤j) (jn : j≤p.length) :
    ∃ q : G.Walk (p.getVert i) (p.getVert j),q.IsPath ∧ Ordered p q ∧ Bounds p q i j ∧
      q.length=j-i ∧ (∀ z∈q.support,z∈p.support) ∧
      (∀ k≤p.length,p.getVert k∈q.support ↔ i≤k ∧ k≤j) := by
  have in' : i≤p.length := ij.trans jn
  let D := p.dropUntil (p.getVert i) (p.getVert_mem_support i)
  let P := p.takeUntil (p.getVert i) (p.getVert_mem_support i)
  have pl : P.length=i := after_takeUntil_index p i in' hp
  have app : P.append D=p := take_spec _ _
  have dl : D.length+i=p.length := by
    have h := congrArg Walk.length app
    rw [length_append] at h
    omega
  have Dp : D.IsPath := hp.dropUntil _
  have coord (s : Nat) : D.getVert s=p.getVert (i+s) := by
    have e := dropUntil_getVert_from_prefix p (p.getVert_mem_support i) s
    change D.getVert s=p.getVert (P.length+s) at e
    rwa [pl] at e
  have jD : D.getVert (j-i)=p.getVert j := by
    rw [coord,show i+(j-i)=j by omega]
  let R := D.takeUntil (D.getVert (j-i)) (D.getVert_mem_support (j-i))
  let q := R.copy rfl jD
  have ql : q.length=j-i := by
    rw [show q=R.copy rfl jD from rfl,length_copy]
    exact after_takeUntil_index D (j-i) (by omega) Dp
  have qcoord (s : Nat) (sq : s≤q.length) : q.getVert s=p.getVert (i+s) := by
    rw [show q=R.copy rfl jD from rfl,getVert_copy]
    have rr : s≤R.length := by simpa [q] using sq
    have e := getVert_takeUntil (D.getVert_mem_support (j-i)) rr
    exact e.trans (coord s)
  have cover (k : Nat) (kn : k≤p.length) : p.getVert k∈q.support ↔ i≤k ∧ k≤j := by
    constructor
    · intro ks
      obtain ⟨s,e,sl⟩ := mem_support_iff_exists_getVert.mp ks
      have hh : i+s≤p.length := by omega
      have eq := hp.getVert_injOn hh kn ((qcoord s sl).symm.trans e)
      omega
    · rintro ⟨lo,hi⟩
      have e := qcoord (k-i) (by omega)
      rw [show i+(k-i)=k by omega] at e
      exact e ▸ q.getVert_mem_support (k-i)
  refine ⟨q,?_,?_,fun k kn h => (cover k kn).mp h,ql,?_,cover⟩
  · simpa [q] using Dp.takeUntil (D.getVert_mem_support (j-i))
  · intro s t sl tl st u v ul vl e f
    have ei := hp.getVert_injOn (by omega : i+s≤p.length) ul ((qcoord s sl).symm.trans e)
    have ej := hp.getVert_injOn (by omega : i+t≤p.length) vl ((qcoord t tl).symm.trans f)
    omega
  · intro z zs
    obtain ⟨s,e,sl⟩ := mem_support_iff_exists_getVert.mp zs
    exact ((qcoord s sl).symm.trans e) ▸ p.getVert_mem_support (i+s)

#print axioms ordered_append
#print axioms spine_segment
end Graffiti189LongestPath.PosaSpine
