import NineBoundary
namespace Graffiti384b.NinePins
open Finset SimpleGraph EarFrame33 EightPins
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A score-two anchor with two private adjacent exterior neighbors and
its triangular ear completes the catalogue bound whenever there are at
most nine exterior contacts. -/
theorem private_triangle_bound (t : (types G).card=31) (q : (nonleaves G).card=31)
    {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let X := high G\A
    (X.filter (fun i => 0<nbr G i A)).card≤9 →
    ∀ w∈A,∀u∈({e,f}:Finset V),∀ b∈A,∀i∈X,∀j∈X,
      i≠j → G.neighborFinset u={w,b} → G.Adj w b → X.filter (G.Adj w)={i,j} →
      G.Adj i j → trianglesAt G w=2 → nbr G i A=1 → nbr G j A=1 → gamma G≤bound G := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  dsimp only
  intro nine w wa u ue b ba i ix j jx ij un wb row edge score ip jp
  by_contra! bad
  change X.filter (G.Adj w)={i,j} at row
  change w∈A at wa; change b∈A at ba; change i∈X at ix; change j∈X at jx
  let E : Finset V := {e,f}
  let D := X.filter (fun z => 2≤nbr G z A)
  let Q := E∪D
  let T := X\D
  obtain ⟨_,ah,_,_,_,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  have ed {z : V} (m : z∈E) : G.degree z=2 := (mem_insert.mp m).elim (fun h => h ▸ de) (fun h => mem_singleton.mp h ▸ df)
  have low {z : V} (zm : z∈E) : z∉high G := by
    intro h; have := (mem_filter.mp h).2; rw [ed zm] at this; omega
  have us := low ue
  have ir : i∈X.filter (G.Adj w) := row ▸ mem_insert_self ..
  have jr : j∈X.filter (G.Adj w) := row ▸ mem_insert_of_mem (mem_singleton_self _)
  have wi := (mem_filter.mp ir).2; have wj := (mem_filter.mp jr).2
  have wu := ((G.mem_neighborFinset ..).mp (show w∈G.neighborFinset u from un ▸ mem_insert_self ..)).symm
  have ua : u∉A := fun m => us (ah m)
  have ui : u≠i := fun h => us (h ▸ (mem_sdiff.mp ix).1)
  have uj : u≠j := fun h => us (h ▸ (mem_sdiff.mp jx).1)
  have ub : u≠b := fun h => us (h ▸ ah ba)
  have bi : b≠i := fun h => (mem_sdiff.mp ix).2 (h ▸ ba)
  have bj : b≠j := fun h => (mem_sdiff.mp jx).2 (h ▸ ba)
  have neighbors : G.neighborFinset w={u,b,i,j} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le (insert_subset ((G.mem_neighborFinset ..).mpr wu)
      (insert_subset ((G.mem_neighborFinset ..).mpr wb) (insert_subset ((G.mem_neighborFinset ..).mpr wi)
        (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr wj)))))
    rw [card_neighborFinset_eq_degree]
    simpa [ub,ui,uj,bi,bj,ij] using SparsePairs.score_two_degree_le_four G t q bad ef de df wa score
  have one : nbr G w A≤1 := by
    have sub : A.filter (G.Adj w)⊆{b} := by
      intro a am; obtain ⟨aa,adj⟩ := mem_filter.mp am
      have az := (G.mem_neighborFinset ..).mpr adj; rw [neighbors] at az
      simp only [mem_insert,mem_singleton] at az ⊢
      rcases az with rfl|eq|rfl|rfl
      · exact (ua aa).elim
      · exact eq
      · exact ((mem_sdiff.mp ix).2 aa).elim
      · exact ((mem_sdiff.mp jx).2 aa).elim
    exact (card_le_card sub).trans_eq (card_singleton b)
  have k2 : nbr G w X=2 := by rw [nbr,row,card_pair ij]
  have priv (a : V) (m : a∈X.filter (G.Adj w)) : nbr G a A=1 := by
    rw [row] at m
    exact (mem_insert.mp m).elim (fun h => h ▸ ip) (fun h => mem_singleton.mp h ▸ jp)
  have tip : Tip G A Q w := private_boundary G ef de df t q bad A rfl wa score one k2 priv nine
  have it' : i∈T := mem_sdiff.mpr ⟨ix,fun m => by have := (mem_filter.mp m).2; change nbr G i A=1 at ip; omega⟩
  have jt' : j∈T := mem_sdiff.mpr ⟨jx,fun m => by have := (mem_filter.mp m).2; change nbr G j A=1 at jp; omega⟩
  have away : Disjoint T (A∪Q) := disjoint_left.mpr (by
    intro v vt vm; obtain ⟨vx,vd⟩ := mem_sdiff.mp vt
    rcases mem_union.mp vm with a|l
    · exact (mem_sdiff.mp vx).2 a
    · exact (mem_union.mp l).elim (fun m => low m (mem_sdiff.mp vx).1) vd)
  have stop (res : ∃ L R,A⊆L ∧ Q⊆R ∧ Frame G L R) : False := by
    obtain ⟨L,R,_,qr,fr⟩ := res
    exact ef (Squares29.sparse G bad _ _ fr e (mem_union_right _ (qr (mem_union_left _ (mem_insert_self ..))))
      f (mem_union_right _ (qr (mem_union_left _ (mem_insert_of_mem (mem_singleton_self _))))) de df)
  rcases flexible_region G tip wi wj edge it' jt' away with done|⟨C,ct,ic,_,fixed,closed⟩
  · exact stop done
  have cx : C⊆X := ct.trans sdiff_subset
  have wc : w∉C := fun h => (mem_sdiff.mp (cx h)).2 wa
  have c2 : nbr G w C≤2 := (card_le_card (filter_subset_filter _ cx)).trans_eq k2
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by rw [t,hs])
  have inE {z : V} (dz : G.degree z=2) : z∈LowSample.twos G := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have ears : E=LowSample.twos G := eq_of_subset_of_card_le (insert_subset (inE de) (singleton_subset_iff.mpr (inE df)))
    (by rw [show E.card=2 from card_pair ef]; exact es.le)
  refine stop (attach_region G tip ic wi (away.mono_left ct) ?_)
  intro v vc
  have vx := cx vc; have vh := (mem_sdiff.mp vx).1; have va := (mem_sdiff.mp vx).2
  have cover (a z : V) (av : G.Adj v a) (vz : G.Adj v z) (az : G.Adj a z) : a∈insert w C := by
    have ag : a∈high G := by
      apply Classical.byContradiction
      intro notHigh
      have upper : G.degree a≤2 := Nat.le_of_not_gt (fun h => notHigh (mem_filter.mpr ⟨mem_univ _,h⟩))
      have inc : {v,z}⊆G.neighborFinset a := insert_subset ((G.mem_neighborFinset ..).mpr av.symm) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr az))
      have size := card_le_card inc; rw [card_pair vz.ne,card_neighborFinset_eq_degree] at size
      have m : a∈E := ears.symm ▸ inE (by omega)
      have adj := (G.mem_neighborFinset ..).mpr av.symm
      exact va ((mem_insert.mp m).elim (fun h => mem_union_left _ (h ▸ adj)) (fun h => mem_union_right _ (mem_singleton.mp h ▸ adj)))
    by_cases am : a∈A∪Q
    · exact mem_insert.mpr (Or.inl (fixed v vc a am av))
    · have an : a∉A := fun h => am (mem_union_left _ h)
      have ad : a∉D := fun h => am (mem_union_right _ (mem_union_right _ h))
      exact mem_insert_of_mem (closed v vc a (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨ag,an⟩,ad⟩) av)
  have cap := local_triangles G vc c2 cover
  have unequal : trianglesAt G v≠2 := fun h => wc (inj vh (ah wa) (h.trans score.symm) ▸ vc)
  have lo := floor v vh
  apply Nat.le_of_not_gt
  intro smallDeg
  have c1 := Nat.choose_le_choose 2 (show nbr G v C≤2 by omega)
  rw [show (2:ℕ).choose 2=1 by decide] at c1; omega

/-- The catalogue bound through nine contacts for the two specified ears.
The exact private-triangle premise is derived afresh in the nine-contact case. -/
theorem at_most_nine (t : (types G).card=31) (q : (nonleaves G).card=31)
    {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (small : (((high G)\(G.neighborFinset e∪G.neighborFinset f)).filter
      (fun i => 0<nbr G i (G.neighborFinset e∪G.neighborFinset f))).card≤9) :
    gamma G≤bound G := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let H := (high G\A).filter (fun z => 0<nbr G z A)
  change H.card≤9 at small
  by_cases old : H.card≤8
  · exact EightPins.at_most_eight G t q ef de df old
  apply Nat.le_of_not_gt; intro bad
  have nine : H.card=9 := by omega
  obtain ⟨w,wa,u,ue,b,ba,i,ix,j,jx,ij,un,wb,row,edge,score,ip,jp⟩ :=
    nine_triangles G t q bad ef de df nine
  exact (Nat.not_lt_of_ge (private_triangle_bound G t q ef de df small w wa u ue b ba i ix j jx ij un wb row edge score ip jp)) bad

/-- Version with the neighbor set of all degree-two vertices. The graph
supplies its own ears through the full 31/31 profile theorem. -/
theorem nine_contacts_bound (t : (types G).card=31) (q : (nonleaves G).card=31)
    (small : let A := (LowSample.twos G).biUnion (G.neighborFinset ·)
      ((high G\A).filter (fun z => 0<nbr G z A)).card≤9) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  obtain ⟨_,count⟩ := TwoEars.profile G t q bad
  obtain ⟨e,f,ef,pair⟩ := card_eq_two.mp count
  have two (z : V) (m : z∈LowSample.twos G) : G.degree z=2 := by
    obtain ⟨vm,off⟩ := mem_sdiff.mp m
    have lo := (mem_filter.mp vm).2
    have hi : G.degree z≤2 := Nat.le_of_not_gt (fun h => off (mem_filter.mpr ⟨mem_univ _,h⟩))
    omega
  have de := two e (pair ▸ mem_insert_self ..)
  have df := two f (pair ▸ mem_insert_of_mem (mem_singleton_self _))
  have ae : (LowSample.twos G).biUnion (G.neighborFinset ·)=G.neighborFinset e∪G.neighborFinset f := by
    rw [pair]; simp
  dsimp only at small; rw [ae] at small
  exact (Nat.not_lt_of_ge (at_most_nine G t q ef de df small)) bad

end Graffiti384b.NinePins
#print axioms Graffiti384b.NinePins.private_triangle_bound
#print axioms Graffiti384b.NinePins.at_most_nine
#print axioms Graffiti384b.NinePins.nine_contacts_bound
