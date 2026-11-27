import FourRingCutAux

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open FourRingBudget FourRingCutAux FourRingCutChoices
noncomputable section
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r)

def minor (A : SimpleGraph U) (r : Bool→U) : SimpleGraph (Piece r) :=
  A.comap Subtype.val

local instance [DecidableRel A.Adj] : DecidableRel (minor A r).Adj :=
  fun x y=>inferInstanceAs (Decidable (A.Adj x.val y.val))

def extend (c : Piece r→Bool) (a b : Bool) (v : U) : Bool :=
  if h : v=r false then a else if h' : v=r true then b else c ⟨v,h,h'⟩

omit [Fintype U] in
theorem extend_false (c : Piece r→Bool) (a b : Bool) :
    extend c a b (r false)=a := by simp [extend]

include L in
omit [Fintype U] in
theorem extend_true (c : Piece r→Bool) (a b : Bool) :
    extend c a b (r true)=b := by simp [extend,L.rootEdge.ne.symm]

omit [Fintype U] in
theorem extend_piece (c : Piece r→Bool) (a b : Bool) (v : Piece r) :
    extend c a b v.val=c v := by simp [extend,v.property.1,v.property.2]

private def PairMap (r : Bool→U) : (Piece r×Piece r)↪(U×U) :=
  ⟨fun x=>(x.1.val,x.2.val),fun _ _ e=>Prod.ext
    (Subtype.ext (congrArg Prod.fst e)) (Subtype.ext (congrArg Prod.snd e))⟩

def rootEnds (q : Option Slot) : U×U :=
  match q with
  | none => (r false,r true)
  | some i => (r i.1,(L.port i).val)

def capActive (c : Piece r→Bool) (a b : Bool) : Finset (Option Slot) :=
  univ.filter (fun i=>extend c a b (L.rootEnds i).1≠extend c a b (L.rootEnds i).2)

omit [Fintype U] in
theorem active_card (c : Piece r→Bool) (a b : Bool) :
    (L.capActive c a b).card=extensionCost (fun s=>c (L.port s)) a b := by
  classical
  let p : Option Slot→Prop :=
    fun i=>extend c a b (L.rootEnds i).1≠extend c a b (L.rootEnds i).2
  have eq : (univ : Finset (Option Slot)) =
      {none,some (false,false),some (false,true),some (true,false),some (true,true)} := by decide
  have tally : (L.capActive c a b).card = ∑ i : Option Slot, if p i then (1:ℕ) else 0 := by
    change (univ.filter p).card=_
    rw [←sum_filter]
    simp
  rw [tally,eq,sum_insert (by decide : (none:Option Slot)∉{some (false,false),some (false,true),some (true,false),some (true,true)}),
    sum_insert (by decide : (some (false,false):Option Slot)∉{some (false,true),some (true,false),some (true,true)}),
    sum_insert (by decide : (some (false,true):Option Slot)∉{some (true,false),some (true,true)}),
    sum_insert (by decide : (some (true,false):Option Slot)∉{some (true,true)}),sum_singleton]
  simp only [p,rootEnds,extend_false,L.extend_true,extend_piece,extensionCost,diff,ite_not]
  omega

/-- Any two-root extension incurs only the internal cut plus
the five possible root-incident crossing edges. -/
theorem cap_cut_upper (c : Piece r→Bool) (a b : Bool) :
    (boundary A (extend c a b)).card ≤ (boundary (minor A r) c).card +
      extensionCost (fun s=>c (L.port s)) a b := by
  classical
  let C := extend c a b
  let I := (boundary (minor A r) c).map (PairMap r)
  let E := (L.capActive c a b).image (fun i=>orientation C (L.rootEnds i).1 (L.rootEnds i).2)
  have activated {i : Option Slot} (m : C (L.rootEnds i).1≠C (L.rootEnds i).2) :
      orientation C (L.rootEnds i).1 (L.rootEnds i).2∈E :=
    mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,m⟩,rfl⟩
  have sub : boundary A C ⊆ I∪E := by
    rintro ⟨x,y⟩ h
    obtain ⟨hx,hy,adj⟩ := mem_boundary.mp h
    by_cases hxr : ∃ s,x=r s
    · obtain ⟨s,rfl⟩ := hxr
      by_cases hyr : ∃ t,y=r t
      · obtain ⟨t,rfl⟩ := hyr
        cases s <;> cases t
        · exact (adj.ne rfl).elim
        · exact mem_union_right _ (by
            have m : C (L.rootEnds none).1≠C (L.rootEnds none).2 := by
              change C (r false)≠C (r true)
              rw [hx,hy]; decide
            simpa only [rootEnds,orientation,hx,if_true] using activated m)
        · exact mem_union_right _ (by
            have m : C (L.rootEnds none).1≠C (L.rootEnds none).2 := by
              change C (r false)≠C (r true)
              rw [hx,hy]; decide
            simpa only [rootEnds,orientation,hy,Bool.false_eq_true,if_false] using activated m)
        · exact (adj.ne rfl).elim
      · let Y : Piece r := ⟨y,fun e=>hyr ⟨false,e⟩, fun e=>hyr ⟨true,e⟩⟩
        obtain ⟨j,eq⟩ := L.exactPort s Y adj
        have ey : (L.port (s,j)).val=y := congrArg Subtype.val eq
        have m : C (L.rootEnds (some (s,j))).1≠C (L.rootEnds (some (s,j))).2 := by
          change C (r s)≠C (L.port (s,j)).val
          rw [ey,hx,hy]; decide
        exact mem_union_right _ (by
          simpa only [rootEnds,ey,orientation,hx,if_true] using activated m)
    · let X : Piece r := ⟨x,fun e=>hxr ⟨false,e⟩, fun e=>hxr ⟨true,e⟩⟩
      by_cases hyr : ∃ t,y=r t
      · obtain ⟨t,rfl⟩ := hyr
        obtain ⟨j,eq⟩ := L.exactPort t X adj.symm
        have ex : (L.port (t,j)).val=x := congrArg Subtype.val eq
        have m : C (L.rootEnds (some (t,j))).1≠C (L.rootEnds (some (t,j))).2 := by
          change C (r t)≠C (L.port (t,j)).val
          rw [ex,hx,hy]; decide
        exact mem_union_right _ (by
          simpa only [rootEnds,ex,orientation,hy,Bool.false_eq_true,if_false] using activated m)
      · let Y : Piece r := ⟨y,fun e=>hyr ⟨false,e⟩, fun e=>hyr ⟨true,e⟩⟩
        have inside : (X,Y)∈boundary (minor A r) c := mem_boundary.mpr
          ⟨by rw [←extend_piece c a b X]; exact hx,
           by rw [←extend_piece c a b Y]; exact hy,adj⟩
        exact mem_union_left _ (mem_map.mpr ⟨(X,Y),inside,rfl⟩)
  have bound := card_le_card sub
  have ball := card_union_le I E
  have io : I.card=(boundary (minor A r) c).card := card_map _
  have ebound : E.card≤extensionCost (fun s=>c (L.port s)) a b := by
    rw [←L.active_card c a b]
    exact card_image_le
  change (boundary A C).card≤_
  omega

include L in
/-- Deleting the cap pair loses no more than one neighbor at any
surviving vertex, using uniqueness of the four ports. -/
theorem minor_degree [DecidableRel A.Adj] (cub : ∀v,A.degree v=3) (x : Piece r) :
    2≤(minor A r).degree x := by
  classical
  let N := A.neighborFinset x.val
  let F := (N.erase (r false)).erase (r true)
  have nS : N.card=3 := cub _
  have at_most_one : r false∉N ∨ r true∉N := by
    by_contra! both
    obtain ⟨j,p⟩ := L.exactPort false x ((mem_neighborFinset A _ _).mp both.1).symm
    obtain ⟨k,q⟩ := L.exactPort true x ((mem_neighborFinset A _ _).mp both.2).symm
    exact Bool.false_ne_true (congrArg Prod.fst (L.port.injective (p.trans q.symm)))
  have low : 2≤F.card := by
    rcases at_most_one with f|t
    · dsimp only [F]
      rw [erase_eq_of_not_mem f]
      by_cases b : r true∈N
      · rw [card_erase_of_mem b,nS]
      · rw [erase_eq_of_not_mem b,nS]; decide
    · have no : r true∉N.erase (r false) := fun e=>t (mem_erase.mp e).2
      dsimp only [F]
      rw [erase_eq_of_not_mem no]
      by_cases b : r false∈N
      · rw [card_erase_of_mem b,nS]
      · rw [erase_eq_of_not_mem b,nS]; decide
  let f : ↥F→(minor A r).neighborSet x := fun v=>
    ⟨⟨v.val,(mem_erase.mp (mem_erase.mp v.property).2).1,(mem_erase.mp v.property).1⟩,
      (mem_neighborFinset A x.val v.val).mp (mem_erase.mp (mem_erase.mp v.property).2).2⟩
  have fi : Function.Injective f := by
    intro u v e
    exact Subtype.ext (congrArg (fun x : (minor A r).neighborSet _=>x.val.val) e)
  have le := Fintype.card_le_of_injective f fi
  rw [Fintype.card_coe,card_neighborSet_eq_degree] at le
  exact low.trans le

include L in
/-- Every mixed cut in a cell has at least two internal edges;
a cheaper one would extend to a trivial cap cut, impossible
at internal degree at least two. -/
theorem mixed_internal_two [DecidableRel A.Adj] (cub : ∀ v,A.degree v=3)
    (small : SmallTrivial A) (c : Piece r→Bool)
    (someTrue : ∃x,c x=true) (someFalse : ∃x,c x=false) :
    2≤(boundary (minor A r) c).card := by
  obtain ⟨u,cu⟩ := someTrue
  obtain ⟨v,cv⟩ := someFalse
  obtain ⟨a,b,co⟩ := extend_with_at_most_two (fun s=>c (L.port s))
  by_contra! low
  have capSize := L.cap_cut_upper c a b
  rcases small (extend c a b) (by omega) with T|F
  · have unique : ∀x,c x=c u→x=u := by
      intro x hx
      apply Subtype.ext
      exact T _ _ ((extend_piece c a b x).trans (hx.trans cu)) ((extend_piece c a b u).trans cu)
    have eq := singleton_colour_boundary (minor A r) c u unique
    have min := L.minor_degree cub u
    omega
  · have unique : ∀x,c x=c v→x=v := by
      intro x hx
      apply Subtype.ext
      exact F _ _ ((extend_piece c a b x).trans (hx.trans cv)) ((extend_piece c a b v).trans cv)
    have eq := singleton_colour_boundary (minor A r) c v unique
    have min := L.minor_degree cub v
    omega

#print axioms cap_cut_upper
#print axioms mixed_internal_two
end
end KelmansCactus.FourRingReplica.Layout
