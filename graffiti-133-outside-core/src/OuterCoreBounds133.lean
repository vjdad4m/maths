import FirstBandFour133

namespace Graffiti133OuterCore
open SimpleGraph Graffiti133 Finset
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def contacts (G : SimpleGraph V) (C : Finset V) (x : V) : Finset V := by
  classical
  exact C.filter (G.Adj x)

theorem mem_contacts {C : Finset V} {x y : V} :
    y ∈ contacts G C x ↔ y∈C ∧ G.Adj x y := by
  classical
  simp [contacts]

noncomputable def exteriorNeighbors (G : SimpleGraph V) (C : Finset V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => y∉C ∧ G.Adj x y)

theorem external_degree_le_core (h4 : FourCycleFree G) (C : Finset V)
    (dom : ∀ z∉C, ∃ w∈C,G.Adj z w) (x : V) (hx : x∉C) :
    (exteriorNeighbors G C x).card ≤ C.card := by
  classical
  let T := Finset.univ.filter (fun y => y∉C ∧ G.Adj x y)
  let pick (y : V) := if h : y∉C then Classical.choose (dom y h) else x
  have pickIs (y : V) (h : y∉C) : pick y∈C ∧ G.Adj y (pick y) := by
    simpa only [pick,dif_pos h] using Classical.choose_spec (dom y h)
  apply Finset.card_le_card_of_injOn (s := T) pick
  · intro y h
    exact (pickIs y (Finset.mem_filter.mp h).2.1).1
  · intro y hy z hz e
    have hy' := (Finset.mem_filter.mp hy).2
    have hz' := (Finset.mem_filter.mp hz).2
    obtain ⟨hyC,hyE⟩ := pickIs y hy'.1
    obtain ⟨_,hzE⟩ := pickIs z hz'.1
    exact h4 x (pick y) y z (fun eq => hx (eq.symm ▸ hyC)) hy'.2 hyE.symm hz'.2 (e.symm ▸ hzE).symm

noncomputable def multi (G : SimpleGraph V) (C : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => y∉C ∧ 2≤(contacts G C y).card)

theorem double_multi_le_pairs (h4 : FourCycleFree G) (C : Finset V) :
    2*(multi G C).card ≤ C.card*(C.card-1) := by
  classical
  let U := {x // x∈multi G C}
  have two (x : U) : ∃ a b, a∈C ∧ b∈C ∧ a≠b ∧ G.Adj x.val a ∧ G.Adj x.val b := by
    have h : 1 < (contacts G C x.val).card := (Finset.mem_filter.mp x.property).2.2
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
    obtain ⟨ac,ea⟩ := mem_contacts.mp ha
    obtain ⟨bc,eb⟩ := mem_contacts.mp hb
    exact ⟨a,b,ac,bc,ne,ea,eb⟩
  let a (x : U) := Classical.choose (two x)
  let b (x : U) := Classical.choose (Classical.choose_spec (two x))
  have prop (x : U) : a x∈C ∧ b x∈C ∧ a x≠b x ∧ G.Adj x.val (a x) ∧ G.Adj x.val (b x) :=
    Classical.choose_spec (Classical.choose_spec (two x))
  let F (p : U×Bool) : V×V := if p.2 then (a p.1,b p.1) else (b p.1,a p.1)
  have facts (p : U×Bool) :
      (F p).1∈C ∧ (F p).2∈C ∧ (F p).1≠(F p).2 ∧
        G.Adj p.1.val (F p).1 ∧ G.Adj p.1.val (F p).2 := by
    obtain ⟨ac,bc,ne,ae,be⟩ := prop p.1
    cases h : p.2
    · exact ⟨by simp [F,h,bc],by simp [F,h,ac],by simpa [F,h] using ne.symm,
        by simp [F,h,be],by simp [F,h,ae]⟩
    · simpa [F,h] using prop p.1
  have orient (x : U) (p q : Bool) (e : F (x,p)=F (x,q)) : p=q := by
    cases p <;> cases q
    · rfl
    · exact ((prop x).2.2.1 (congrArg Prod.snd e)).elim
    · exact ((prop x).2.2.1 (congrArg Prod.fst e)).elim
    · rfl
  have inj : Function.Injective F := by
    rintro ⟨x,p⟩ ⟨y,q⟩ e
    have fe := facts (x,p)
    have ge := facts (y,q)
    have xy : x=y := by
      by_contra! ne
      have notVal : x.val≠y.val := fun v => ne (Subtype.ext v)
      rw [←e] at ge
      exact fe.2.2.1 (h4 x.val y.val _ _ notVal fe.2.2.2.1 ge.2.2.2.1 fe.2.2.2.2 ge.2.2.2.2)
    subst y
    exact Prod.ext rfl (orient x p q e)
  have lk := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (U×Bool)))
    (t := C.offDiag) F (fun p _ => Finset.mem_offDiag.mpr
      ⟨(facts p).1,(facts p).2.1,(facts p).2.2.1⟩) inj.injOn
  rw [Finset.card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] at lk
  have diagEq : C.diag = C.image (fun x => (x,x)) := by
    ext p
    constructor
    · intro h
      obtain ⟨hp,eq⟩ := Finset.mem_diag.mp h
      exact Finset.mem_image.mpr ⟨p.1,hp,Prod.ext rfl eq⟩
    · rintro h
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_diag.mpr ⟨hx,rfl⟩
  have diagCard : C.diag.card=C.card := by
    rw [diagEq,Finset.card_image_of_injective _ (fun _ _ e => congrArg Prod.fst e)]
  have disj : Disjoint C.diag C.offDiag := by
    apply Finset.disjoint_left.mpr
    intro _ h f
    exact (Finset.mem_offDiag.mp f).2.2 (Finset.mem_diag.mp h).2
  have ee : C.offDiag.card+C.card = C.card*C.card := by
    calc C.offDiag.card+C.card = C.diag.card+C.offDiag.card := by omega
      _ = (C.diag ∪ C.offDiag).card := (Finset.card_union_of_disjoint disj).symm
      _ = C.card*C.card := by rw [Finset.diag_union_offDiag,Finset.card_product]
  rw [Nat.mul_sub, Nat.mul_one]
  omega

theorem core_nine_multiples (h4 : FourCycleFree G) (C : Finset V) (cap : C.card≤9) :
    (multi G C).card≤36 := by
  have h := double_multi_le_pairs h4 C
  have ub := Nat.mul_le_mul cap (show C.card-1≤8 by omega)
  omega

#print axioms core_nine_multiples
#print axioms external_degree_le_core
#print axioms double_multi_le_pairs
end Graffiti133OuterCore
