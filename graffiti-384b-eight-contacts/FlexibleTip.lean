import EightDegree
namespace Graffiti384b.EightPins
open Finset SimpleGraph EarFrame33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All pins are supported except x, which can be finished by one further opposite neighbor. -/
structure Tip (L R : Finset V) (x : V) : Prop where
  dis : Disjoint L R
  onSide : x∈L
  near : ∃ z∈R,G.Adj x z
  left : ∀ a∈L,a≠x → 2≤nbr G a R
  right : ∀ a∈R,2≤nbr G a L

omit [Fintype V] in
private theorem advance {L R : Finset V} {x y : V} (tip : Tip G L R x) (xy : G.Adj x y)
    (yl : y∉L) (yr : y∉R) : Tip G (insert y R) L y := by
  refine ⟨disjoint_insert_left.mpr ⟨yl,tip.dis.symm⟩,mem_insert_self ..,⟨x,tip.onSide,xy.symm⟩,?_,?_⟩
  · intro a am ne; exact tip.right a ((mem_insert.mp am).resolve_left ne)
  · intro a am
    by_cases eq : a=x
    · subst a; obtain ⟨z,zm,xz⟩ := tip.near
      exact PinnedColor34.two G (fun (h:z=y) => yr (h ▸ zm)) xz xy (mem_insert_of_mem zm) (mem_insert_self ..)
    · exact (tip.left a am eq).trans (Repair.nbr_mono G _ (subset_insert ..))

/-- A terminal x is on the first side, uses only the extra vertices S,
and has a predecessor outside the fixed boundary except possibly the root w. -/
private def Route (P Q S : Finset V) (w x : V) : Prop :=
  ∃ L R,Tip G L R x ∧ P⊆L ∧ Q⊆R ∧ L∪R⊆(P∪Q)∪S ∧
    ∃ z∈R,z∈insert w S ∧ G.Adj x z

omit [Fintype V] in
private theorem wider {P Q S T : Finset V} {w x : V} (route : Route G P Q S w x) (sub : S⊆T) :
    Route G P Q T w x := by
  obtain ⟨L,R,tip,p,q,sub',z,zm,zs,xz⟩ := route
  exact ⟨L,R,tip,p,q,sub'.trans (union_subset_union Subset.rfl sub),z,zm,insert_subset_insert _ sub zs,xz⟩

omit [Fintype V] in
private theorem extend {P Q S : Finset V} {w x y : V} (route : Route G P Q S w x)
    (xy : G.Adj x y) (xs : x∈S) (outside : y∉(P∪Q)∪S) : Route G Q P (insert y S) w y := by
  obtain ⟨L,R,tip,p,q,sub,_⟩ := route
  have nl : y∉L := fun m => outside (sub (mem_union_left _ m))
  have nr : y∉R := fun m => outside (sub (mem_union_right _ m))
  refine ⟨insert y R,L,advance G tip xy nl nr,q.trans (subset_insert ..),p,?_,x,tip.onSide,by simp [xs],xy.symm⟩
  intro a am
  rw [union_comm Q P]
  rcases mem_union.mp am with m|m
  · rcases mem_insert.mp m with rfl|m
    · exact mem_union_right _ (mem_insert_self ..)
    · exact (union_subset_union Subset.rfl (subset_insert y S)) (sub (mem_union_right _ m))
  · exact (union_subset_union Subset.rfl (subset_insert y S)) (sub (mem_union_left _ m))

omit [Fintype V] in
private theorem finish {P Q S : Finset V} {w x y : V} (r : Route G P Q S w x) (xy : G.Adj x y)
    (yq : y∈Q) (yw : y≠w) (ys : y∉S) : ∃ L R,P⊆L ∧ Q⊆R ∧ Frame G L R := by
  obtain ⟨L,R,tip,p,q,_,z,zm,zs,xz⟩ := r
  refine ⟨L,R,p,q,tip.dis,?_,tip.right⟩
  intro a am; by_cases ax : a=x
  · subst a
    exact PinnedColor34.two G (fun (h:y=z) => (mem_insert.mp (h ▸ zs : y∈insert w S)).elim yw ys) xy xz (q yq) zm
  · exact tip.left a am ax

omit [Fintype V] in
private theorem start {P Q : Finset V} {w i j : V} (tip : Tip G P Q w)
    (wi : G.Adj w i) (wj : G.Adj w j) (ij : G.Adj i j)
    (off : Disjoint ({i,j}:Finset V) (P∪Q)) :
    Route G P Q {i,j} w i ∧ Route G Q P {i,j} w i := by
  have fresh {z : V} (m : z∈({i,j}:Finset V)) : z∉P ∧ z∉Q :=
    ⟨fun h => disjoint_left.mp off m (mem_union_left _ h),fun h => disjoint_left.mp off m (mem_union_right _ h)⟩
  have fi := fresh (mem_insert_self i {j}); have fj := fresh (mem_insert_of_mem (mem_singleton_self j) : j∈({i,j}:Finset V))
  have t1 := advance G tip wj fj.1 fj.2
  have t2 := advance G t1 ij.symm (by simp [ij.ne,fi.2]) fi.1
  refine ⟨⟨insert i P,insert j Q,t2,subset_insert ..,subset_insert ..,?_,j,mem_insert_self ..,by simp,ij⟩,
    ⟨insert i Q,P,advance G tip wi fi.1 fi.2,subset_insert ..,Subset.rfl,?_,w,tip.onSide,mem_insert_self ..,wi.symm⟩⟩
  · intro a am; simp only [mem_union,mem_insert,mem_singleton] at am ⊢; tauto
  · intro a am; simp only [mem_union,mem_insert,mem_singleton] at am ⊢; tauto

/-- Grow both possible parities from a triangle. Either the pending root can be
protected with the fixed boundary, or the private pair belongs to a set closed
under exterior neighbors and missing every fixed pin except w. -/
theorem flexible_region {P Q X : Finset V} {w i j : V} (tip : Tip G P Q w)
    (wi : G.Adj w i) (wj : G.Adj w j) (ij : G.Adj i j) (ix : i∈X) (jx : j∈X)
    (dis : Disjoint X (P∪Q)) :
    (∃ L R,P⊆L ∧ Q⊆R ∧ Frame G L R) ∨ ∃ C⊆X,i∈C ∧ j∈C ∧
      (∀ v∈C,∀ a∈P∪Q,G.Adj v a → a=w) ∧ (∀ v∈C,∀ a∈X,G.Adj v a → a∈C) := by
  classical
  by_cases done : ∃ L R,P⊆L ∧ Q⊆R ∧ Frame G L R
  · exact Or.inl done
  right
  let ok (S : Finset V) := S⊆X ∧ i∈S ∧ j∈S ∧ ∀ x∈S,Route G P Q S w x ∧ Route G Q P S w x
  have sub : ({i,j}:Finset V)⊆X := insert_subset ix (singleton_subset_iff.mpr jx)
  have init : ok {i,j} := by
    refine ⟨sub,by simp,by simp,?_⟩
    intro x xm; rcases mem_insert.mp xm with rfl|m
    · exact start G tip wi wj ij (dis.mono_left sub)
    · rw [mem_singleton.mp m,pair_comm i j]; exact start G tip wj wi ij.symm (by rw [pair_comm j i]; exact dis.mono_left sub)
  let family := (univ : Finset (Finset V)).filter ok
  obtain ⟨C,cm,big⟩ := exists_max_image family Finset.card ⟨{i,j},mem_filter.mpr ⟨mem_univ _,init⟩⟩
  obtain ⟨cx,ic,jc,routes⟩ := (mem_filter.mp cm).2
  refine ⟨C,cx,ic,jc,?_,?_⟩
  · intro v vm a am va; by_contra aw
    have ac : a∉C := fun h => disjoint_left.mp dis (cx h) am
    rcases mem_union.mp am with ap|aq
    · obtain ⟨R,L,q,p,h⟩ := finish G (routes v vm).2 va ap aw ac
      exact done ⟨L,R,p,q,h.1.symm,h.2.2,h.2.1⟩
    · exact done (finish G (routes v vm).1 va aq aw ac)
  · intro v vm a ax va; by_contra ac
    have off : a∉P∪Q := fun h => disjoint_left.mp dis ax h
    have off' : a∉Q∪P := by rwa [union_comm]
    have more : ok (insert a C) := by
      refine ⟨insert_subset ax cx,mem_insert_of_mem ic,mem_insert_of_mem jc,?_⟩
      intro y ym; rcases mem_insert.mp ym with rfl|m
      · exact ⟨extend G (routes v vm).2 va vm (fun h => (mem_union.mp h).elim off' ac),extend G (routes v vm).1 va vm (fun h => (mem_union.mp h).elim off ac)⟩
      · exact ⟨wider G (routes y m).1 (subset_insert ..),wider G (routes y m).2 (subset_insert ..)⟩
    have h := big (insert a C) (mem_filter.mpr ⟨mem_univ _,more⟩)
    rw [card_insert_of_not_mem ac] at h; omega

end Graffiti384b.EightPins
#print axioms Graffiti384b.EightPins.flexible_region
