import PosaOrderedPair189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaOrderedPair
open Graffiti189LongestPath.CycleTwoCuts
set_option warningAsError true
set_option maxHeartbeats 5000000
namespace Graffiti189LongestPath.PosaRouteCut
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure Cut {a b : V} (p q : G.Walk a b) (i : Nat) where
  pre : G.Walk a (p.getVert i)
  suf : G.Walk (p.getVert i) b
  split : pre.append suf=q
  prePath : pre.IsPath
  sufPath : suf.IsPath
  preOrder : Ordered p pre
  sufOrder : Ordered p suf
  preBounds : Bounds p pre 0 i
  sufBounds : Bounds p suf i p.length
  keepsPre : ∀ j≤p.length,j≤i → p.getVert j∈q.support → p.getVert j∈pre.support
  keepsSuf : ∀ j≤p.length,i≤j → p.getVert j∈q.support → p.getVert j∈suf.support

omit [DecidableEq V] in
theorem Cut.pre_inc {a b : V} {p q : G.Walk a b} {i : Nat} (c : Cut p q i) :
    ∀ z∈c.pre.support,z∈q.support := by
  intro z h
  rw [←c.split,mem_support_append_iff]
  exact Or.inl h

omit [DecidableEq V] in
theorem Cut.suf_inc {a b : V} {p q : G.Walk a b} {i : Nat} (c : Cut p q i) :
    ∀ z∈c.suf.support,z∈q.support := by
  intro z h
  rw [←c.split,mem_support_append_iff]
  exact Or.inr h

omit [DecidableEq V] in
theorem Cut.pre_coord {a b : V} {p q : G.Walk a b} {i : Nat} (c : Cut p q i)
    (s : Nat) (sl : s≤c.pre.length) :
    c.pre.getVert s=q.getVert s := by
  have ee := (congrArg (fun W : G.Walk a b => W.getVert s) c.split).symm
  rw [getVert_append] at ee
  by_cases eq : s=c.pre.length
  · rw [eq,if_neg (Nat.lt_irrefl _),Nat.sub_self,getVert_zero] at ee
    simpa only [eq,getVert_length] using ee.symm
  rw [if_pos (by omega)] at ee
  exact ee.symm

omit [DecidableEq V] in
theorem Cut.suf_coord {a b : V} {p q : G.Walk a b} {i : Nat} (c : Cut p q i)
    (s : Nat) : c.suf.getVert s=q.getVert (c.pre.length+s) := by
  have ee := (congrArg (fun W : G.Walk a b => W.getVert (c.pre.length+s)) c.split).symm
  rw [getVert_append,if_neg (by omega),show c.pre.length+s-c.pre.length=s by omega] at ee
  exact ee.symm

/-- Cut a monotone spine route at a present spine position; the cut
retains every earlier/later spine position on the appropriate side. -/
theorem cut_ordered_route {a b : V} (p q : G.Walk a b) (hp : p.IsPath) (qp : q.IsPath)
    (qo : Ordered p q) (i : Nat) (il : i≤p.length) (hit : p.getVert i∈q.support) :
    Nonempty (Cut p q i) := by
  let P := q.takeUntil (p.getVert i) hit
  let Q := q.dropUntil (p.getVert i) hit
  have pp : P.IsPath := qp.takeUntil hit
  have qq : Q.IsPath := qp.dropUntil hit
  have app : P.append Q=q := take_spec _ hit
  have pl (j : Nat) (h : j≤P.length) : P.getVert j=q.getVert j :=
    getVert_takeUntil hit h
  have ql (j : Nat) : Q.getVert j=q.getVert (P.length+j) :=
    dropUntil_getVert_from_prefix q hit j
  have qlen : P.length+Q.length=q.length := by rw [←length_append,app]
  have pivot : q.getVert P.length=p.getVert i := by
    have h := pl P.length (by omega)
    rw [getVert_length] at h
    exact h.symm
  have preOrder : Ordered p P := by
    intro s t sl tl st u v ul vl e f
    exact qo s t (by omega) (by omega) st u v ul vl
      ((pl s sl).symm.trans e) ((pl t tl).symm.trans f)
  have sufOrder : Ordered p Q := by
    intro s t sl tl st u v ul vl e f
    exact qo (P.length+s) (P.length+t) (by omega) (by omega) (by omega) u v ul vl
      ((ql s).symm.trans e) ((ql t).symm.trans f)
  have preBounds : Bounds p P 0 i := by
    intro j jl jP
    obtain ⟨s,e,sl⟩ := mem_support_iff_exists_getVert.mp jP
    have eq := ((pl s sl).symm.trans e)
    refine ⟨Nat.zero_le _,?_⟩
    by_cases h : s=P.length
    · rw [h] at eq
      have w := hp.getVert_injOn jl il (eq.symm.trans pivot)
      omega
    exact (qo s P.length (by omega) (by omega) (by omega) j i jl il eq pivot).le
  refine ⟨⟨P,Q,app,pp,qq,preOrder,sufOrder,preBounds,?_,?_,?_⟩⟩
  · intro j jl jQ
    obtain ⟨s,e,sl⟩ := mem_support_iff_exists_getVert.mp jQ
    have eq := ((ql s).symm.trans e)
    refine ⟨?_,jl⟩
    by_cases h : s=0
    · subst s
      rw [getVert_zero] at e
      have w := hp.getVert_injOn il jl e
      omega
    exact (qo P.length (P.length+s) (by omega) (by omega) (by omega)
      i j il jl pivot eq).le
  · intro j jl ji jq
    obtain ⟨s,e,sl⟩ := mem_support_iff_exists_getVert.mp jq
    have le : s≤P.length := by
      apply Nat.le_of_not_gt
      intro p
      exact (not_lt_of_ge ji) (qo P.length s (by omega) sl p i j il jl pivot e)
    exact ((pl s le).trans e) ▸ P.getVert_mem_support s
  · intro j jl ij jq
    obtain ⟨s,e,sl⟩ := mem_support_iff_exists_getVert.mp jq
    have le : P.length≤s := by
      apply Nat.le_of_not_gt
      intro p
      exact (not_lt_of_ge ij) (qo s P.length sl (by omega) p j i jl il e pivot)
    have f := (ql (s-P.length)).trans (show q.getVert (P.length+(s-P.length))=p.getVert j by
      rw [show P.length+(s-P.length)=s by omega,e])
    exact f ▸ Q.getVert_mem_support (s-P.length)

omit [DecidableEq V] in
theorem separated_cuts_disjoint {a b : V} {p q : G.Walk a b} (qp : q.IsPath)
    (qo : Ordered p q) (hp : p.IsPath) {i j : Nat}
    (ij : i<j) (in' : i≤p.length) (jn : j≤p.length)
    (X : Cut p q i) (Y : Cut p q j) :
    List.Disjoint X.pre.support Y.suf.support := by
  have XL : X.pre.length+X.suf.length=q.length := by rw [←length_append,X.split]
  have YL : Y.pre.length+Y.suf.length=q.length := by rw [←length_append,Y.split]
  have x : q.getVert X.pre.length=p.getVert i := by
    have eq := X.pre_coord X.pre.length (by omega)
    rw [getVert_length] at eq
    exact eq.symm
  have y : q.getVert Y.pre.length=p.getVert j := by
    have eq := Y.pre_coord Y.pre.length (by omega)
    rw [getVert_length] at eq
    exact eq.symm
  have lt : X.pre.length<Y.pre.length := by
    by_cases e : X.pre.length=Y.pre.length
    · have vv := x.symm.trans (e ▸ y)
      have eq := hp.getVert_injOn in' jn vv
      omega
    by_contra hn
    have jj := qo Y.pre.length X.pre.length (by omega) (by omega) (by omega) j i jn in' y x
    omega
  intro z xp ys
  obtain ⟨s,se,sl⟩ := mem_support_iff_exists_getVert.mp xp
  obtain ⟨t,te,tl⟩ := mem_support_iff_exists_getVert.mp ys
  have u := qp.getVert_injOn (by omega : s≤q.length) (by omega : Y.pre.length+t≤q.length)
    ((X.pre_coord s sl).symm.trans (se.trans (te.symm.trans (Y.suf_coord t))))
  omega

#print axioms cut_ordered_route
#print axioms separated_cuts_disjoint
end Graffiti189LongestPath.PosaRouteCut
