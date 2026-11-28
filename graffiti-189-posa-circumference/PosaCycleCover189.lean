import PosaMaxCover189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaOrderedPair
open Graffiti189LongestPath.PosaSpliceCommon Graffiti189LongestPath.PosaMaxCover
open private Graffiti189LongestPath.FanRoutable.path_append_separated from FanLower189
set_option warningAsError true
set_option maxHeartbeats 6000000
namespace Graffiti189LongestPath.PosaCycleCover
variable {V : Type*} {G : SimpleGraph V}

theorem ordered_reverse {a b u v : V} {p : G.Walk a b} {q : G.Walk u v}
    (h : Ordered p q) : Ordered p.reverse q.reverse := by
  intro s t sl tl st i j il jl e f
  rw [length_reverse] at sl tl il jl
  simp only [getVert_reverse] at e f
  have lt := h (q.length-t) (q.length-s) (by omega) (by omega) (by omega)
    (p.length-j) (p.length-i) (by omega) (by omega) f e
  omega

def reversePair {a b : V} {p : G.Walk a b} (R : OrderedPair p) : OrderedPair p.reverse :=
  ⟨R.left.reverse,R.right.reverse,R.leftPath.reverse,R.rightPath.reverse,
    ordered_reverse R.leftOrder,ordered_reverse R.rightOrder,
    (by
      intro z zl zr
      exact (R.only z (by simpa only [support_reverse,List.mem_reverse] using zl)
        (by simpa only [support_reverse,List.mem_reverse] using zr)).elim Or.inr Or.inl),
    (by
      obtain ⟨z,h,za,zb⟩ := R.internal_exact
      exact ⟨z,by simpa only [support_reverse,List.mem_reverse] using h,zb,za⟩)⟩

def unreversePair {a b : V} {p : G.Walk a b} (R : OrderedPair p.reverse) : OrderedPair p :=
  ⟨R.left.reverse,R.right.reverse,R.leftPath.reverse,R.rightPath.reverse,
    (by simpa only [reverse_reverse] using ordered_reverse R.leftOrder),
    (by simpa only [reverse_reverse] using ordered_reverse R.rightOrder),
    (by
      intro z zl zr
      exact (R.only z (by simpa only [support_reverse,List.mem_reverse] using zl)
        (by simpa only [support_reverse,List.mem_reverse] using zr)).elim Or.inr Or.inl),
    (by
      obtain ⟨z,h,zb,za⟩ := R.internal_exact
      exact ⟨z,by simpa only [support_reverse,List.mem_reverse] using h,za,zb⟩)⟩

theorem hits_reverse {a b : V} {p : G.Walk a b} (R : OrderedPair p) (j : Nat) :
    Hits (reversePair R) j ↔ Hits R (p.length-j) := by
  simp only [Hits,reversePair,getVert_reverse,support_reverse,List.mem_reverse]

theorem hits_unreverse {a b : V} {p : G.Walk a b} (R : OrderedPair p.reverse)
    (i : Nat) (il : i≤p.length) :
    Hits (unreversePair R) i ↔ Hits R (p.length-i) := by
  simp only [Hits,unreversePair,getVert_reverse,support_reverse,List.mem_reverse,
    show p.length-(p.length-i)=i by omega]

variable [DecidableEq V]

theorem optimal_right {a b : V} {p : G.Walk a b} (hp : p.IsPath) (R : OrderedPair p)
    (max : ∀ T : OrderedPair p,(covered T).card≤(covered R).card)
    (i : Nat) (ip : 0<i) (il : i<p.length)
    (edge : G.Adj b (p.getVert i)) : Hits R i := by
  apply Classical.byContradiction
  intro no
  let j := p.length-i
  have jj : p.length-j=i := by dsimp [j]; omega
  have ne : ¬Hits (reversePair R) j := by
    rw [hits_reverse,jj]
    exact no
  have ed : G.Adj b (p.reverse.getVert j) := by simpa only [getVert_reverse,jj] using edge
  obtain ⟨T,hit,keep⟩ := augment_missing_left_neighbor hp.reverse (reversePair R) j
    (by dsimp [j]; omega) (by simp only [length_reverse,j]; omega) ed ne
  let U := unreversePair T
  have add : Hits U i := (hits_unreverse T i il.le).mpr hit
  have sub : covered R⊆covered U := by
    intro s hs
    obtain ⟨sN,sh⟩ := (mem_covered R s).mp hs
    have d : p.length-(p.length-s)=s := by omega
    have reverseHit : Hits (reversePair R) (p.length-s) := by rw [hits_reverse,d]; exact sh
    have v := keep (p.length-s) (by simp only [length_reverse]; omega) reverseHit
    exact (mem_covered U s).mpr ⟨sN,(hits_unreverse T s sN).mpr v⟩
  have eq := eq_of_subset_of_card_le sub (max U)
  have h : i∈covered U := (mem_covered U i).mpr ⟨il.le,add⟩
  exact no ((mem_covered R i).mp (eq.symm ▸ h)).2

omit [DecidableEq V] in
private theorem cycle_of_left_internal {a b : V} {p : G.Walk a b} (R : OrderedPair p)
    (internal : ∃ z,z∈R.left.support ∧ z≠a ∧ z≠b) :
    ∃ c : G.Walk a a,c.IsCycle ∧
      (∀ z,z∈c.support ↔ z∈R.left.support ∨ z∈R.right.support) := by
  obtain ⟨z,zL,za,zb⟩ := internal
  obtain ⟨n,nv,nl⟩ := mem_support_iff_exists_getVert.mp zL
  have np : 0<n := by
    apply Nat.pos_of_ne_zero
    intro e
    rw [e,getVert_zero] at nv
    exact za nv.symm
  have nN : n<R.left.length := by
    apply lt_of_le_of_ne nl
    intro e
    rw [e,getVert_length] at nv
    exact zb nv.symm
  have dn : ¬R.left.Nil := not_nil_iff_lt_length.mpr (by omega)
  let L := R.left.tail
  have ls : L.support=R.left.support.tail := support_tail_of_not_nil _ dn
  have lp : L.IsPath := by
    rw [isPath_def,ls]
    exact R.leftPath.support_nodup.tail
  have La : a∉L.support := by
    have no := R.leftPath.support_nodup
    rw [←cons_support_tail _ dn,List.nodup_cons] at no
    exact no.1
  let e := R.left.adj_snd dn
  have beta : R.left.snd≠b := by
    intro eq
    have same : R.left.getVert 1=R.left.getVert R.left.length := eq.trans R.left.getVert_length.symm
    have one := R.leftPath.getVert_injOn (by change 1≤R.left.length; omega) (by simp) same
    omega
  have leftSup (w : V) (wl : w∈L.support) : w∈R.left.support :=
    List.mem_of_mem_tail (ls ▸ wl)
  let M := L.append R.right.reverse
  have mp : M.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated lp
    R.rightPath.reverse (by
      intro w wl wr
      have r := R.only w (leftSup w wl) (by simpa only [support_reverse,List.mem_reverse] using wr)
      exact r.elim (fun h => (La (h ▸ wl)).elim) id)
  have fresh : s(a,R.left.snd)∉M.edges := by
    intro h
    rw [show M=L.append R.right.reverse from rfl,edges_append,List.mem_append] at h
    rcases h with h|h
    · exact La (L.fst_mem_support_of_mem_edges h)
    have bR := R.right.reverse.snd_mem_support_of_mem_edges h
    have E := R.only R.left.snd (R.left.getVert_mem_support 1)
      (by simpa only [support_reverse,List.mem_reverse] using bR)
    exact E.elim e.ne.symm beta
  let C := Walk.cons e M
  have cp : C.IsCycle := (cons_isCycle_iff _ _).mpr ⟨mp,fresh⟩
  have eq : C=R.left.append R.right.reverse := by
    change Walk.cons e (L.append R.right.reverse)=_
    rw [←cons_append,cons_tail_eq _ dn]
  exact ⟨C,cp,fun z => by
    rw [eq,mem_support_append_iff,support_reverse,List.mem_reverse]⟩

omit [DecidableEq V] in
theorem cycle_of_ordered_pair {a b : V} {p : G.Walk a b} (R : OrderedPair p) :
    ∃ c : G.Walk a a,c.IsCycle ∧
      (∀ z,z∈c.support ↔ z∈R.left.support ∨ z∈R.right.support) := by
  obtain ⟨z,zc,za,zb⟩ := R.internal_exact
  rcases zc with l|r
  · exact cycle_of_left_internal R ⟨z,l,za,zb⟩
  obtain ⟨c,cp,sup⟩ := cycle_of_left_internal (OrderedPair.swap R) ⟨z,r,za,zb⟩
  exact ⟨c,cp,fun z => (sup z).trans Or.comm⟩

#print axioms optimal_right
#print axioms cycle_of_ordered_pair
end Graffiti189LongestPath.PosaCycleCover
