import PairTests180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- Price the extra independent markings when one section misses a marked bag. -/
theorem mark_price (G : SimpleGraph B) (r : B) (I J P : Finset B) :
    weightedLeaves G (eligible I P r)≤weightedLeaves G (eligible J P r)+(I\J).card := by
  classical
  apply Finset.sup_le
  intro T tm
  have sub : eligible I P r∩leaves T⊆(eligible J P r∩leaves T)∪(I\J) := by
    intro x xm
    simp only [mem_inter,eligible_iff,mem_union,mem_sdiff] at xm ⊢
    by_cases eq : x=r
    · subst x;tauto
    · tauto
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_right
    (le_sup (f:=fun T => (eligible J P r∩leaves T).card) tm) _))

omit [Fintype V] [Fintype B] in
/-- Bipartite coloring on chosen representatives and additional independent
vertices that have no edge to the representative of their own bag. -/
theorem over_color (h : Bags H G f) (t : B→V) (sec : Function.LeftInverse f t)
    (Z : Finset B) (col : TwoColor G Z) (X : Finset V) (ind : Indep H X)
    (over : ∀ x∈X,f x∈Z) (avoid : ∀ x∈X,¬H.Adj x (t (f x))) :
    TwoColor H (Z.image t∪X) := by
  classical
  obtain ⟨c,ok⟩ := (color_function ..).mp col
  have within {x : V} (xm : x∈Z.image t∪X) : f x∈Z := by
    rcases mem_union.mp xm with old|extra
    · obtain ⟨i,iz,rfl⟩ := mem_image.mp old; rwa [sec i]
    · exact over x extra
  apply (color_function ..).mpr
  refine ⟨fun x => c (f x),fun x xm y ym ed => ?_⟩
  by_cases diff : f x≠f y
  · exact ok _ (within xm) _ (within ym) ((h.across diff).mp ed)
  have same := not_not.mp diff
  exfalso
  rcases mem_union.mp xm with a|a <;> rcases mem_union.mp ym with b|b
  · obtain ⟨i,_,rfl⟩ := mem_image.mp a; obtain ⟨j,_,rfl⟩ := mem_image.mp b
    rw [sec i,sec j] at same;exact ed.ne (congrArg t same)
  · obtain ⟨i,_,rfl⟩ := mem_image.mp a;rw [sec i] at same
    exact avoid y b (same ▸ ed.symm)
  · obtain ⟨j,_,rfl⟩ := mem_image.mp b;rw [sec j] at same
    exact avoid x a (same.symm ▸ ed)
  · exact ind x a y b ed.ne ed

/-- All protected markings lift across arbitrary nonempty substitution
bags when the quotient has no universal vertex. -/
theorem protected_lift (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (nh : ∀ i,¬Universal G i) (r : V) (p : Bool) (A : Finset V) (ai : Indep H A)
    (old : Protected G (f r) p (A.image f)) : Protected H r p A := by
  classical
  let P := parity H r p
  let Q := parity G (f r) p
  let I := A.image f
  let U := eligible A P r
  obtain ⟨s,t,ss,st,root,off,even,inside,avoid⟩ := h.sections r p A ai
  let J := pull t A
  let X := (A∩P)\univ.image t
  obtain ⟨Z,col,pins,base⟩ := old
  change I∩insert (f r) Q⊆Z at pins
  change 1+I.card+Q.card≤weightedLeaves G (eligible I Q (f r))+Z.card at base
  have over {x : V} (xa : x∈A) (xp : x∈insert r P) : f x∈Z := by
    apply pins (mem_inter.mpr ⟨mem_image_of_mem _ xa,?_⟩)
    by_cases same : f x=f r
    · exact mem_insert.mpr (Or.inl same)
    · have xr : x≠r := fun eq => same (congrArg f eq)
      have pm := (mem_parity H r x p).mp ((mem_insert.mp xp).resolve_left xr)
      have dist : H.dist x r=G.dist (f x) (f r) := by simpa [same] using h.metric gc hn x r
      exact mem_insert_of_mem ((mem_parity G (f r) (f x) p).mpr (dist ▸ pm))
  have paint := over_color h t st Z col X
    (fun x xm y ym => ai x (mem_inter.mp (mem_sdiff.mp xm).1).1 y (mem_inter.mp (mem_sdiff.mp ym).1).1)
    (fun x xm => over (mem_inter.mp (mem_sdiff.mp xm).1).1 (mem_insert_of_mem (mem_inter.mp (mem_sdiff.mp xm).1).2)) avoid
  refine ⟨Z.image t∪X,paint,?_,?_⟩
  · intro x xm
    obtain ⟨xa,xp⟩ := mem_inter.mp xm
    have z := over xa xp
    by_cases rep : x∈univ.image t
    · obtain ⟨i,_,rfl⟩ := mem_image.mp rep;rw [st i] at z
      exact mem_union_left _ (mem_image_of_mem _ z)
    · have xr : x≠r := by
        rintro rfl
        have choose := inside (f x) (by simpa only [root] using xa)
        exact rep (mem_image.mpr ⟨f x,mem_univ _,choose.symm.trans root⟩)
      exact mem_union_right _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨xa,(mem_insert.mp xp).resolve_left xr⟩,rep⟩)
  · have dis : Disjoint (Z.image t) X := disjoint_left.mpr (fun x m extra =>
      (mem_sdiff.mp extra).2 (image_subset_image (subset_univ Z) m))
    have size : (Z.image t∪X).card=Z.card+X.card := by rw [card_union_of_disjoint dis,card_image_of_injective _ st.injective]
    have sub : J⊆I := by
      intro i im
      exact mem_image.mpr ⟨t i,mem_pull.mp im,st i⟩
    have gap := card_sdiff_add_card_eq_card sub
    have price := mark_price G (f r) I J Q
    have lf := h.liftLeaves gc (three_of_nohub G gc hn nh) nh s ss U
    obtain ⟨ue,pe⟩ := h.eligible_pull gc r p A s t ss root off even
    change pull s U=eligible J Q (f r) at ue
    rw [ue] at lf
    have ac := section_count t st.injective A
    change A.card=J.card+(A\univ.image t).card at ac
    have pc := section_count s ss.injective P
    change pull s P=Q at pe
    rw [pe] at pc
    have eq : U\univ.image s=(A∪P)\univ.image s := by
      ext x
      have rin : r∈univ.image s := root ▸ mem_image_of_mem s (mem_univ (f r))
      simp only [U,mem_sdiff,eligible_iff,mem_union]
      by_cases same : x=r
      · subst x;simp [rin]
      · simp [same]
    rw [eq] at lf
    have extras := extra_count s t A P inside
    change (A\univ.image t).card+(P\univ.image s).card≤((A∪P)\univ.image s).card+X.card at extras
    change 1+A.card+P.card≤weightedLeaves H U+(Z.image t∪X).card
    omega

#print axioms mark_price
#print axioms over_color
#print axioms protected_lift
end Minimal180.Transversals
