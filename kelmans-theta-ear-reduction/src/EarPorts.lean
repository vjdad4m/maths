import PentagonCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.EarPorts
open SquareCap (boundary)
open PentagonCap (attach attach_boundary attach_degree_inside SmallFourTrivial)
open PentagonProfile (Port mismatch portCount portWeight portCount_complement)
noncomputable section

variable {V T : Type*} [Fintype V] [Fintype T]

private theorem in_boundary {G : SimpleGraph V} {c : V → Bool} {e : V × V} :
    e ∈ boundary G c ↔ c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2 := by
  classical
  simp [boundary]

private theorem singleton_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→Bool) (x : V) (hx : c x=true)
    (uniq : ∀ y,c y=true→y=x) :
    (boundary G c).card = G.degree x := by
  classical
  let f : V → V × V := fun v => (x,v)
  have equal : boundary G c = (G.neighborFinset x).image f := by
    ext z
    obtain ⟨u,v⟩ := z
    constructor
    · intro h
      obtain ⟨hu,_,huv⟩ := in_boundary.mp h
      have e := uniq u hu
      refine mem_image.mpr ⟨v,(mem_neighborFinset G x v).mpr (e ▸ huv),?_⟩
      exact Prod.ext e.symm rfl
    · intro h
      obtain ⟨w,hw,eq⟩ := mem_image.mp h
      have eq' : (x,w) = (u,v) := eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq'
      have a := (mem_neighborFinset G x w).mp hw
      have no : c w = false := by
        by_contra! e
        have t : c w = true := by cases h : c w <;> simp_all
        have v_eq := uniq w t
        exact a.ne v_eq.symm
      exact in_boundary.mpr ⟨hx,no,a⟩
  rw [equal,card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),
    card_neighborFinset_eq_degree]


private theorem three_avoiding [DecidableEq V] (large : 4≤Fintype.card V) (v : V) :
    ∃ x y z : V, x≠v ∧ y≠v ∧ z≠v ∧ x≠y ∧ x≠z ∧ y≠z := by
  let S := (univ : Finset V).erase v
  have sn : 3≤S.card := by
    change 3≤((univ : Finset V).erase v).card
    rw [card_erase_of_mem (mem_univ v),card_univ]
    omega
  obtain ⟨a,as,b,bs,ab⟩ := one_lt_card.mp (by omega : 1<S.card)
  have s : ({a,b}:Finset V).card=2 := by simp [card_insert_of_not_mem,ab]
  obtain ⟨c,cs,away⟩ := exists_mem_not_mem_of_card_lt_card (by omega : ({a,b}:Finset V).card<S.card)
  have ne : c≠a ∧ c≠b := by simpa using away
  exact ⟨a,b,c,(mem_erase.mp as).1,(mem_erase.mp bs).1,(mem_erase.mp cs).1,
    ab,ne.1.symm,ne.2.symm⟩

/-- Five wires with distinct gadget endpoints also have distinct
exterior endpoints in this cyclic-five class. This handles the
only possible degeneracy after absorbing an adjacent contact pair.

The graph is written with the gadget as the left summand so
we can count five distinct wires before knowing that the
function assigning exterior contacts is injective. -/
theorem exterior_contacts_injective
    [DecidableEq V] {Q : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    {left : Port ↪ T} {right : Port → V} [DecidableRel (attach Q G left right).Adj]
    (three : Fin 3 ↪ T) (large : 4≤Fintype.card V)
    (cub : ∀ v,(attach Q G left right).degree (Sum.inr v)=3)
    (strong : SmallFourTrivial (attach Q G left right)) :
    Function.Injective right := by
  classical
  intro i j same
  by_contra ne
  let v := right i
  let d : V→Bool := fun w=>decide (w=v)
  let E : Finset Port := univ.filter (fun i=>right i=v)
  have k2 : 2≤E.card := by
    apply Nat.succ_le_of_lt
    exact one_lt_card.mpr ⟨i,by simp [E,v],j,by simp [E,v,same],ne⟩
  have deg := cub v
  rw [attach_degree_inside] at deg
  change E.card + G.degree v=3 at deg
  have c0 : (boundary Q (fun _=>true)).card=0 := by simp [boundary]
  have c1 : (boundary G d).card=G.degree v :=
    singleton_boundary G d v (by simp [d]) (fun y hy=>by simpa [d] using hy)
  have p1 : portCount (Function.Embedding.refl Port) (d∘right) true=E.card := by
    simp [portCount,E,d]
  have mm :
      mismatch left (fun _=>true) (d∘right) =
        portCount (Function.Embedding.refl Port) (d∘right) false := by
    simp [mismatch, portCount, ←Bool.eq_false_iff]
  have all := portCount_complement (Function.Embedding.refl Port) (d∘right)
  let c : T⊕V→Bool := Sum.elim (fun _=>true) d
  have count : (boundary (attach Q G left right) c).card≤4 := by
    change (boundary (attach Q G left right) (Sum.elim (fun _=>true) d)).card≤4
    rw [attach_boundary,c0,c1,mm]
    rw [p1] at all
    omega
  obtain ⟨b,tiny⟩ := strong c count
  cases b
  · obtain ⟨a,b,z,av,bv,zv,ab,az,bz⟩ := three_avoiding large v
    have eq := tiny (Sum.inr a) (Sum.inr b) (Sum.inr z)
      (by simp [c,d,av]) (by simp [c,d,bv]) (by simp [c,d,zv])
    rcases eq with e|e|e
    · exact ab (Sum.inr_injective e)
    · exact az (Sum.inr_injective e)
    · exact bz (Sum.inr_injective e)
  · have eq := tiny (Sum.inl (three 0)) (Sum.inl (three 1)) (Sum.inl (three 2)) rfl rfl rfl
    rcases eq with e|e|e
    · exact (by decide : (0:Fin 3)≠1) (three.injective (Sum.inl_injective e))
    · exact (by decide : (0:Fin 3)≠2) (three.injective (Sum.inl_injective e))
    · exact (by decide : (1:Fin 3)≠2) (three.injective (Sum.inl_injective e))

#print axioms exterior_contacts_injective

end
end KelmansCactus.AtomicBridge.EarPorts
