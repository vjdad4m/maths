import PentagonCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.EarRelease
open PentagonCap (attach attach_degree_outside SmallFourTrivial)
open PentagonProfile (Port)
noncomputable section

universe u
variable {V : Type u}

abbrev Rest (p : Port ↪ V) := {x : V // x≠p 1 ∧ x≠p 4}

private theorem selected_distinct (p : Port↪V) : p 1≠p 4 :=
  fun h=>(by decide : (1:Port)≠4) (p.injective h)

/-- The old 7 vertices retain labels 0..6; the two absorbed
outside vertices get labels 7 and 8. -/
def gadget (p : Port↪V) (j : Fin 9) : V⊕Fin 7 :=
  if h : j.val<7 then Sum.inr ⟨j.val,h⟩
  else if j=7 then Sum.inl (p 1) else Sum.inl (p 4)

private theorem fin9_region (i : Fin 9) : i.val<7 ∨ i=7 ∨ i=8 := by
  revert i
  decide

private theorem gadget_old (p : Port↪V) (i : Fin 9) (h : i.val<7) :
    gadget p i = Sum.inr ⟨i.val,h⟩ := by simp [gadget,h]

private theorem gadget_seven (p : Port↪V) : gadget p 7=Sum.inl (p 1) := by
  have low : ¬ ((7:Fin 9).val<7) := by decide
  simp [gadget,low]

private theorem gadget_eight (p : Port↪V) : gadget p 8=Sum.inl (p 4) := by
  have low : ¬ ((8:Fin 9).val<7) := by decide
  simp [gadget,low]

private theorem gadget_injective (p : Port↪V) : Function.Injective (gadget p) := by
  intro a b equal
  rcases fin9_region a with aa|rfl|rfl <;> rcases fin9_region b with bb|rfl|rfl
  · rw [gadget_old _ _ aa,gadget_old _ _ bb] at equal
    exact Fin.ext (congrArg (fun x : Fin 7=>x.val) (Sum.inr_injective equal))
  · rw [gadget_old _ _ aa,gadget_seven] at equal
    exact Sum.noConfusion equal
  · rw [gadget_old _ _ aa,gadget_eight] at equal
    exact Sum.noConfusion equal
  · rw [gadget_seven,gadget_old _ _ bb] at equal
    exact Sum.noConfusion equal
  · rfl
  · rw [gadget_seven,gadget_eight] at equal
    exact (selected_distinct p (Sum.inl_injective equal)).elim
  · rw [gadget_eight,gadget_old _ _ bb] at equal
    exact Sum.noConfusion equal
  · rw [gadget_eight,gadget_seven] at equal
    exact ((selected_distinct p).symm (Sum.inl_injective equal)).elim
  · rfl

def releasedMap [DecidableEq V] (p : Port↪V) : (Fin 9 ⊕ Rest p) ≃ (V⊕Fin 7) := by
  let f : Fin 9⊕Rest p → V⊕Fin 7 := Sum.elim (gadget p) (fun x=>Sum.inl x.val)
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (gadget_injective p h)
      | inr b =>
        change gadget p a=Sum.inl b.val at h
        rcases fin9_region a with aa|rfl|rfl
        · rw [gadget_old _ _ aa] at h
          exact Sum.noConfusion h
        · rw [gadget_seven] at h
          exact (b.property.1 (Sum.inl_injective h.symm)).elim
        · rw [gadget_eight] at h
          exact (b.property.2 (Sum.inl_injective h.symm)).elim
    | inr a => cases b with
      | inl b =>
        change Sum.inl a.val=gadget p b at h
        rcases fin9_region b with bb|rfl|rfl
        · rw [gadget_old _ _ bb] at h
          exact Sum.noConfusion h
        · rw [gadget_seven] at h
          exact (a.property.1 (Sum.inl_injective h)).elim
        · rw [gadget_eight] at h
          exact (a.property.2 (Sum.inl_injective h)).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext (Sum.inl_injective h))
  · intro x
    cases x with
    | inl x =>
      by_cases h1 : x=p 1
      · exact ⟨Sum.inl 7,(gadget_seven p).trans (congrArg Sum.inl h1.symm)⟩
      · by_cases h4 : x=p 4
        · exact ⟨Sum.inl 8,(gadget_eight p).trans (congrArg Sum.inl h4.symm)⟩
        · exact ⟨Sum.inr ⟨x,h1,h4⟩,rfl⟩
    | inr i =>
      let v : Fin 9 := ⟨i.val,by have h:=i.isLt; omega⟩
      exact ⟨Sum.inl v,gadget_old p v i.isLt⟩

def newArm (r : Port↪Fin 7) (i : Port) : Fin 9 :=
  if i=1 then 7 else if i=4 then 8 else ⟨(r i).val, by have h:=(r i).isLt; omega⟩

private theorem arm_seven (r : Port↪Fin 7) (i : Port) : newArm r i=7 ↔ i=1 := by
  by_cases p : i=1
  · simp [newArm,p]
  · by_cases q : i=4
    · simp [newArm,p,q]
    · simp only [newArm,p,q,if_false]
      constructor
      · intro h
        have eq := congrArg (fun x : Fin 9=>x.val) h
        change (r i).val=7 at eq
        have low := (r i).isLt
        omega
      · exact False.elim

private theorem arm_eight (r : Port↪Fin 7) (i : Port) : newArm r i=8 ↔ i=4 := by
  by_cases p : i=1
  · simp [newArm,p]
  · by_cases q : i=4
    · simp [newArm,p,q]
    · simp only [newArm,p,q,if_false]
      constructor
      · intro h
        have eq := congrArg (fun x : Fin 9=>x.val) h
        change (r i).val=8 at eq
        have low := (r i).isLt
        omega
      · exact False.elim

private theorem arm_old (r : Port↪Fin 7) (i : Port) (p : i≠1) (q : i≠4) :
    (newArm r i).val=(r i).val := by simp [newArm,p,q]

def armEmbedding (r : Port↪Fin 7) : Port↪Fin 9 :=
  ⟨newArm r,by
    intro i j eq
    by_cases a : i=1
    · exact a.trans ((arm_seven r j).mp (eq.symm.trans ((arm_seven r i).mpr a))).symm
    by_cases b : i=4
    · exact b.trans ((arm_eight r j).mp (eq.symm.trans ((arm_eight r i).mpr b))).symm
    have c : j≠1 := fun h=>a ((arm_seven r i).mp (eq.trans ((arm_seven r j).mpr h)))
    have d : j≠4 := fun h=>b ((arm_eight r i).mp (eq.trans ((arm_eight r j).mpr h)))
    apply r.injective
    apply Fin.ext
    exact (arm_old r i a b).symm.trans ((congrArg Fin.val eq).trans (arm_old r j c d))⟩

private theorem unique_out_neighbor [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (degree : G.degree a=2) (known : G.Adj a b) :
    ∃! v : V, v≠a ∧ v≠b ∧ G.Adj a v := by
  have bne : b∈G.neighborFinset a := (mem_neighborFinset _ _ _).mpr known
  have size : ((G.neighborFinset a).erase b).card=1 := by
    rw [card_erase_of_mem bne,card_neighborFinset_eq_degree,degree]
  obtain ⟨v,eq⟩ := card_eq_one.mp size
  have here : v∈(G.neighborFinset a).erase b := eq.symm ▸ mem_singleton_self v
  have adj := (mem_neighborFinset _ _ _).mp (mem_erase.mp here).2
  refine ⟨v,⟨adj.ne.symm,(mem_erase.mp here).1,adj⟩,?_⟩
  intro z hz
  have e : z∈(G.neighborFinset a).erase b :=
    mem_erase.mpr ⟨hz.2.1,(mem_neighborFinset _ _ _).mpr hz.2.2⟩
  rwa [eq,mem_singleton] at e

/-- The two absorbed contacts are replaced by their unique other
outside neighbors. The three untouched ports are unchanged. -/
structure Released (G : SimpleGraph V) (p : Port↪V) where
  next1 : Rest p
  next4 : Rest p
  end1 : ∀ v : Rest p,G.Adj (p 1) v.val ↔ v=next1
  end4 : ∀ v : Rest p,G.Adj (p 4) v.val ↔ v=next4

def releasedOfAdjacent [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {p : Port↪V}
    (d1 : G.degree (p 1)=2) (d4 : G.degree (p 4)=2) (edge : G.Adj (p 1) (p 4)) :
    Released G p := by
  let a := unique_out_neighbor d1 edge
  let b := unique_out_neighbor d4 edge.symm
  let a0 : Rest p := ⟨a.exists.choose,a.exists.choose_spec.1,a.exists.choose_spec.2.1⟩
  let b0 : Rest p := ⟨b.exists.choose,b.exists.choose_spec.2.1,b.exists.choose_spec.1⟩
  have aEdge : G.Adj (p 1) a0.val := a.exists.choose_spec.2.2
  have bEdge : G.Adj (p 4) b0.val := b.exists.choose_spec.2.2
  refine ⟨a0,b0,?_,?_⟩
  · intro v
    constructor
    · intro e
      obtain ⟨u,_,un⟩ := a
      exact Subtype.ext ((un _ ⟨v.property.1,v.property.2,e⟩).trans
        (un _ ⟨a0.property.1,a0.property.2,aEdge⟩).symm)
    · rintro rfl
      exact aEdge
  · intro v
    constructor
    · intro e
      obtain ⟨u,_,un⟩ := b
      exact Subtype.ext ((un _ ⟨v.property.2,v.property.1,e⟩).trans
        (un _ ⟨b0.property.2,b0.property.1,bEdge⟩).symm)
    · rintro rfl
      exact bEdge

def contacts {G : SimpleGraph V} {p : Port↪V} (L : Released G p) (i : Port) : Rest p :=
  if a : i=1 then L.next1 else if b : i=4 then L.next4 else
    ⟨p i,fun h=>a (p.injective h),fun h=>b (p.injective h)⟩

private theorem contact1 {G : SimpleGraph V} {p : Port↪V} (L : Released G p) :
    contacts L 1=L.next1 := by simp [contacts]

private theorem contact4 {G : SimpleGraph V} {p : Port↪V} (L : Released G p) :
    contacts L 4=L.next4 := by simp [contacts]

private theorem contact_old {G : SimpleGraph V} {p : Port↪V} (L : Released G p)
    (i : Port) (a : i≠1) (b : i≠4) :
    (contacts L i).val=p i := by simp [contacts,a,b]

private abbrev releasedOld (G : SimpleGraph V) (p : Port↪V) : SimpleGraph (Rest p) :=
  G.comap Subtype.val

private abbrev releasedNew (G : SimpleGraph V) (P : SimpleGraph (Fin 7)) (p : Port↪V)
    (r : Port↪Fin 7) : SimpleGraph (Fin 9) := (attach G P p r).comap (gadget p)

private theorem actual_wires {G : SimpleGraph V} {P : SimpleGraph (Fin 7)}
    {p : Port↪V} (r : Port↪Fin 7) (L : Released G p) (v : Fin 9) (w : Rest p) :
    (attach G P p r).Adj (gadget p v) (Sum.inl w.val) ↔
      ∃ i,armEmbedding r i=v ∧ contacts L i=w := by
  rcases fin9_region v with old|rfl|rfl
  · rw [gadget_old _ _ old]
    change (∃ i,p i=w.val ∧ r i=⟨v.val,old⟩) ↔ _
    constructor
    · rintro ⟨i,a,b⟩
      have h1 : i≠1 := fun e=>w.property.1 (((congrArg p e).symm.trans a).symm)
      have h4 : i≠4 := fun e=>w.property.2 (((congrArg p e).symm.trans a).symm)
      refine ⟨i,Fin.ext ?_,Subtype.ext ?_⟩
      · change (newArm r i).val=v.val
        exact (arm_old r i h1 h4).trans (congrArg Fin.val b)
      · exact (contact_old L i h1 h4).trans a
    · rintro ⟨i,a,b⟩
      change newArm r i=v at a
      have h1 : i≠1 := by
        intro h
        have nv := ((arm_seven r i).mpr h)
        have e := congrArg Fin.val (a.symm.trans nv)
        change v.val=7 at e
        omega
      have h4 : i≠4 := by
        intro h
        have nv := ((arm_eight r i).mpr h)
        have e := congrArg Fin.val (a.symm.trans nv)
        change v.val=8 at e
        omega
      have pa : p i=w.val := (contact_old L i h1 h4).symm.trans (congrArg Subtype.val b)
      have ra : r i=⟨v.val,old⟩ := Fin.ext
        ((arm_old r i h1 h4).symm.trans (congrArg Fin.val a))
      exact ⟨i,pa,ra⟩
  · rw [gadget_seven]
    change G.Adj (p 1) w.val ↔ _
    rw [L.end1]
    constructor
    · intro e
      exact ⟨1,(arm_seven r 1).mpr rfl,(contact1 L).trans e.symm⟩
    · rintro ⟨i,a,b⟩
      obtain rfl := (arm_seven r i).mp a
      exact b.symm.trans (contact1 L)
  · rw [gadget_eight]
    change G.Adj (p 4) w.val ↔ _
    rw [L.end4]
    constructor
    · intro e
      exact ⟨4,(arm_eight r 4).mpr rfl,(contact4 L).trans e.symm⟩
    · rintro ⟨i,a,b⟩
      obtain rfl := (arm_eight r i).mp a
      exact b.symm.trans (contact4 L)

/-- Re-encode the actual released graph before requiring that the
replacement contacts are distinct. The gadget is the embedding
side and its new wire endpoints are already distinct. -/
def releasedIso [DecidableEq V] {G : SimpleGraph V} {P : SimpleGraph (Fin 7)} {p : Port↪V}
    (r : Port↪Fin 7) (L : Released G p) :
    attach (releasedNew G P p r) (releasedOld G p) (armEmbedding r) (contacts L)
      ≃g attach G P p r := by
  refine { toEquiv := releasedMap p, map_rel_iff' := ?_ }
  intro v w
  cases v with
  | inl v => cases w with
    | inl w => rfl
    | inr w => exact actual_wires r L v w
  | inr v => cases w with
    | inl w =>
      exact ⟨fun e => (actual_wires r L w v).mp e.symm,
        fun h => ((actual_wires r L w v).mpr h).symm⟩
    | inr w => rfl

#print axioms releasedIso
end
end KelmansCactus.AtomicBridge.EarRelease
