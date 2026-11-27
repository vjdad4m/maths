import HighEarShared33

namespace Graffiti384b.HighEar
open Finset SimpleGraph EarAnchor
open private CubicShore.half_tight from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Adjacent unordered pairs in a given vertex set. -/
def pairs (D : Finset V) : Finset (Finset V) :=
  (D.powersetCard 2).filter (fun p => ∀ x∈p,∀ y∈p,x≠y → H.Adj x y)

theorem pair_mem {D E : Finset V} : E∈pairs H D ↔ ∃ x∈D,∃ y∈D,H.Adj x y ∧ E={x,y} := by
  constructor
  · intro m
    obtain ⟨p,cl⟩ := mem_filter.mp m
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp p
    obtain ⟨x,y,ne,rfl⟩ := card_eq_two.mp sz
    have xmem : x∈({x,y} : Finset V) := mem_insert_self ..
    have ymem : y∈({x,y} : Finset V) := mem_insert_of_mem (mem_singleton_self _)
    exact ⟨x,sub xmem,y,sub ymem,cl x xmem y ymem ne,rfl⟩
  · rintro ⟨x,xm,y,ym,edge,rfl⟩
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset xm (singleton_subset_iff.mpr ym),card_pair edge.ne⟩,?_⟩
    intro p hp q hq ne
    rcases (show p=x ∨ p=y by simpa using hp) with rfl|rfl <;>
      rcases (show q=_ ∨ q=_ by simpa only [mem_insert,mem_singleton] using hq) with rfl|rfl <;>
      first | exact (ne rfl).elim | exact edge | exact edge.symm

theorem pairs_insert {D : Finset V} {x : V} (off : x∉D) :
    (pairs H (insert x D)).card=(pairs H D).card+nbr H x D := by
  classical
  let f (y : V) : Finset V := {x,y}
  let M := D.filter (H.Adj x)
  have eq : pairs H (insert x D)=pairs H D ∪ M.image f := by
    ext E; constructor
    · intro m
      obtain ⟨v,vm,w,wm,vw,rfl⟩ := (pair_mem H).mp m
      rcases mem_insert.mp vm with rfl|vD
      · have wd := (mem_insert.mp wm).resolve_left vw.ne.symm
        exact mem_union_right _ (mem_image.mpr ⟨w,mem_filter.mpr ⟨wd,vw⟩,rfl⟩)
      rcases mem_insert.mp wm with rfl|wD
      · exact mem_union_right _ (mem_image.mpr ⟨v,mem_filter.mpr ⟨vD,vw.symm⟩,pair_comm ..⟩)
      · exact mem_union_left _ ((pair_mem H).mpr ⟨v,vD,w,wD,vw,rfl⟩)
    · intro m
      rcases mem_union.mp m with p|q
      · obtain ⟨v,vm,w,wm,vw,rfl⟩ := (pair_mem H).mp p
        exact (pair_mem H).mpr ⟨v,mem_insert_of_mem vm,w,mem_insert_of_mem wm,vw,rfl⟩
      · obtain ⟨y,ym,rfl⟩ := mem_image.mp q
        obtain ⟨yd,xy⟩ := mem_filter.mp ym
        exact (pair_mem H).mpr ⟨x,mem_insert_self ..,y,mem_insert_of_mem yd,xy,rfl⟩
  have dis : Disjoint (pairs H D) (M.image f) := by
    apply disjoint_left.mpr; intro E em fm
    obtain ⟨y,_,rfl⟩ := mem_image.mp fm
    exact off ((mem_powersetCard.mp (mem_filter.mp em).1).1 (mem_insert_self ..))
  have ci : (M.image f).card=M.card := card_image_of_injOn (by
    intro y ym z _ eq
    have m : y∈f z := eq ▸ (show y∈f y from mem_insert_of_mem (mem_singleton_self _))
    exact (mem_insert.mp m).resolve_left (mem_filter.mp ym).2.ne.symm |> mem_singleton.mp)
  rw [eq,card_union_of_disjoint dis,ci]; rfl

def exterior (e a c : V) := (H.neighborFinset a)\{e,c}
def additional (e a c : V) := (H.neighborFinset a∩H.neighborFinset c).erase e

theorem additional_mem {e a c w : V} : w∈additional H e a c ↔ w≠e ∧ H.Adj a w ∧ H.Adj c w := by
  simp [additional]

theorem exact_count {e a c : V} (ear : H.neighborFinset e={a,c}) (ea : H.Adj e a)
    (ec : H.Adj e c) (ac : H.Adj a c) :
    let D := exterior H e a c
    D.card+2=H.degree a ∧ trianglesAt H a=1+(additional H e a c).card+(pairs H D).card := by
  classical
  let D := exterior H e a c
  have em : e∈H.neighborFinset a := (H.mem_neighborFinset _ _).mpr ea.symm
  have cm : c∈H.neighborFinset a := (H.mem_neighborFinset _ _).mpr ac
  have eD : e∉D := fun m => (mem_sdiff.mp m).2 (mem_insert_self ..)
  have cD : c∉D := fun m => (mem_sdiff.mp m).2 (mem_insert_of_mem (mem_singleton_self _))
  have off : e∉insert c D := fun m => (mem_insert.mp m).elim ec.ne eD
  have split : H.neighborFinset a=insert e (insert c D) := by
    ext y; by_cases ye : y=e
    · subst y; simp [em]
    by_cases yc : y=c
    · subst y; simp [cm]
    simp [D,exterior,ye,yc]
  have sz := card_neighborFinset_eq_degree H a
  rw [split,card_insert_of_not_mem off,card_insert_of_not_mem cD] at sz
  change D.card+2=H.degree a ∧ _
  refine ⟨by omega,?_⟩
  have one : nbr H e (insert c D)=1 := by
    have eq : (insert c D).filter (H.Adj e)={c} := by
      ext y; constructor
      · intro m
        obtain ⟨ym,ey⟩ := mem_filter.mp m
        have ny := (H.mem_neighborFinset _ _).mpr ey; rw [ear] at ny
        rcases mem_insert.mp ny with ya|yc
        · subst y
          rcases mem_insert.mp ym with h|ad
          · exact (ac.ne h).elim
          · exact ((H.loopless a) ((H.mem_neighborFinset _ _).mp (mem_sdiff.mp ad).1)).elim
        · exact yc
      · intro m; have h := mem_singleton.mp m; subst y
        exact mem_filter.mpr ⟨mem_insert_self ..,ec⟩
    simp [nbr,eq]
  have common : nbr H c D=(additional H e a c).card := by
    unfold nbr; congr 1; ext y
    simp only [D,exterior,mem_filter,mem_sdiff,H.mem_neighborFinset,mem_insert,mem_singleton,additional_mem]
    constructor
    · rintro ⟨⟨ay,no⟩,cy⟩; exact ⟨fun h => no (Or.inl h),ay,cy⟩
    · rintro ⟨ye,ay,cy⟩; exact ⟨⟨ay,fun o => o.elim ye cy.ne.symm⟩,cy⟩
  change (pairs H (H.neighborFinset a)).card=1+(additional H e a c).card+(pairs H D).card
  rw [split,pairs_insert H off,pairs_insert H cD,one,common]; omega

/-- A degree-four endpoint has two exterior neighbors joined by an edge.
Either neither sees the other endpoint (score two), or both do (score four). -/
theorem four_endpoint {e a c : V} (de : H.degree e=2) (da : H.degree a=4)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C) :
    let D := exterior H e a c
    D.card=2 ∧ (∃ x y,H.Adj x y ∧ D={x,y}) ∧
      ((additional H e a c=∅ ∧ trianglesAt H a=2) ∨ (additional H e a c=D ∧ trianglesAt H a=4)) := by
  classical
  let D := exterior H e a c
  let M := additional H e a c
  have es : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  obtain ⟨ds,score⟩ := exact_count H es ea ec ac
  change D.card+2=H.degree a at ds
  change trianglesAt H a=1+M.card+(pairs H D).card at score
  have two : D.card=2 := by omega
  have sub : M⊆D := by
    intro y ym; obtain ⟨ye,ay,cy⟩ := (additional_mem H).mp ym
    exact mem_sdiff.mpr ⟨(H.mem_neighborFinset _ _).mpr ay,by simpa using And.intro ye cy.ne.symm⟩
  have cap := card_le_card sub
  have capP := card_filter_le (D.powersetCard 2) (fun p => ∀ x∈p,∀ y∈p,x≠y → H.Adj x y)
  change (pairs H D).card≤(D.powersetCard 2).card at capP
  rw [card_powersetCard,two,Nat.choose_self] at capP
  have lo : 2≤trianglesAt H a := by
    have diff : trianglesAt H a≠1 := fun h => ea.ne (inj ((ear_one H de pos).trans h.symm))
    have := pos a; omega
  have both : (pairs H D).card=1 ∧ ((M=∅ ∧ trianglesAt H a=2) ∨ (M=D ∧ trianglesAt H a=4)) := by
    by_cases empty : M=∅
    · rw [empty,card_empty] at score
      exact ⟨by omega,Or.inl ⟨empty,by omega⟩⟩
    obtain ⟨w,wm⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨we,aw,cw⟩ := (additional_mem H).mp wm
    have big := (CubicShore.square_scores H de ea ec ac pos inj half five aw cw we).1
    exact ⟨by omega,Or.inr ⟨eq_of_subset_of_card_le sub (by omega),by omega⟩⟩
  obtain ⟨E,em⟩ := card_pos.mp (show 0<(pairs H D).card by omega)
  obtain ⟨x,xm,y,ym,xy,_⟩ := (pair_mem H).mp em
  exact ⟨two,⟨x,y,xy,(eq_of_subset_of_card_le (insert_subset xm (singleton_subset_iff.mpr ym))
    (by rw [two,card_pair xy.ne])).symm⟩,both.2⟩

theorem degree_sum {e a c : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C) :
    9≤H.degree a+H.degree c ∧
    ((additional H e a c).card=1 → 5≤H.degree a ∧ 5≤H.degree c) := by
  have ⟨la,lc⟩ := CubicShore.endpoints H de ea ec ac pos inj half five
  have comm : additional H e a c=additional H e c a := by simp [additional,inter_comm]
  have at4 {u v : V} (eu : H.Adj e u) (ev : H.Adj e v) (uv : H.Adj u v) (d : H.degree u=4) :
      ((additional H e u v).card=0 ∧ trianglesAt H u=2) ∨
      ((additional H e u v).card=2 ∧ trianglesAt H u=4) := by
    obtain ⟨two,_,h|h⟩ := four_endpoint H de d eu ev uv pos inj half five
    · exact Or.inl ⟨by rw [h.1,card_empty],h.2⟩
    · exact Or.inr ⟨by rw [h.1,two],h.2⟩
  have diff : trianglesAt H a≠trianglesAt H c := fun h => ac.ne (inj h)
  have bad (da : H.degree a=4) (dc : H.degree c=4) : False := by
    have l := at4 ea ec ac da
    have r := at4 ec ea ac.symm dc
    rw [← comm] at r; omega
  refine ⟨?_,?_⟩
  · apply Nat.le_of_not_gt; intro small; exact bad (by omega) (by omega)
  intro count
  have na : H.degree a≠4 := fun d => by have := at4 ea ec ac d; omega
  have nc : H.degree c≠4 := fun d => by have h := at4 ec ea ac.symm d; rw [← comm] at h; omega
  omega

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.exact_count
#print axioms Graffiti384b.HighEar.four_endpoint
#print axioms Graffiti384b.HighEar.degree_sum
