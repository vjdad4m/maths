import CreditEnds31
namespace Graffiti384b.EarCredit
open SimpleGraph Finset EarFrame33 HighEar
open private Seven.compatible from SevenContact
open private CubicShore.square_frame from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- If the pivot misses one endpoint, each additional common neighbor must
occupy the same side of its four pinned neighbors as the other endpoint. -/
private theorem missed {e a b x : V} (ea : H.Adj e a) (eb : H.Adj e b) (ab : a≠b)
    (xe : ¬H.Adj x e) (xa : x≠a) (xb : x≠b) (xne : x≠e)
    (dx : H.degree x=4) (sx : trianglesAt H x=5) (miss : ¬H.Adj x b)
    (rest : ∀ w,w≠e → 3≤H.degree w) (half : Fintype.card V≤2*gamma H) :
    (additional H e a b).card≤1 ∧ ((additional H e a b).Nonempty → H.Adj x a) := by
  classical
  let C := additional H e a b
  obtain ⟨P,Q,un,ps,qs,pf,px,qx⟩ := Frontier31.pivot_frame H dx sx
  have en : e∉P∪Q := fun m => xe ((H.mem_neighborFinset ..).mp (un ▸ m))
  have bn : b∉P∪Q := fun m => miss ((H.mem_neighborFinset ..).mp (un ▸ m))
  have force (R F : Finset V) (eq : R∪F=H.neighborFinset x) (fr : Frame H R F)
      (rx : 2≤nbr H x R) (fx : 2≤nbr H x F) (ao : a∉F) : C⊆R := by
    intro t tm
    obtain ⟨te,at',bt⟩ := (additional_mem H).mp tm
    have xt : x≠t := fun h => miss (h ▸ bt.symm)
    have er : e∉R := fun m => xe ((H.mem_neighborFinset ..).mp (eq ▸ mem_union_left F m))
    have bf : b∉F := fun m => miss ((H.mem_neighborFinset ..).mp (eq ▸ mem_union_right R m))
    have sh : Frame H {e,t} {a,b} := CubicShore.square_frame H ea eb at' bt te.symm ab
    by_contra off
    have ar : Disjoint ({e,t}:Finset V) R := by simpa [disjoint_left] using And.intro er off
    have bf' : Disjoint ({a,b}:Finset V) F := by simpa [disjoint_left] using And.intro ao bf
    have out : x∉({e,t}:Finset V)∪{a,b} := by simp [xne,xt,xa,xb]
    have pr (w : V) (wm : w∉({e,t}:Finset V)∪{a,b}) : 3≤H.degree w :=
      rest w (fun z => wm (z ▸ mem_union_left _ (mem_insert_self ..)))
    exact Seven.compatible H sh ⟨fr.1.symm,fr.2.2,fr.2.1⟩ ((union_comm F R).trans eq) out ar bf' fx rx pr half
  have swap : Frame H Q P := ⟨pf.1.symm,pf.2.2,pf.2.1⟩
  have an : a∉C := fun h => ((additional_mem H).mp h).2.1.ne rfl
  have sz {R : Finset V} (rs : R.card=2) (am : a∈R) (sub : C⊆R) : C.card≤1 := by
    have low := card_le_card (insert_subset am sub); rw [card_insert_of_not_mem an,rs] at low; omega
  by_cases ap : a∈P
  · have aq : a∉Q := fun m => disjoint_left.mp pf.1 ap m
    exact ⟨sz ps ap (force P Q un pf px qx aq),fun _ => (H.mem_neighborFinset ..).mp (un ▸ mem_union_left Q ap)⟩
  by_cases aq : a∈Q
  · exact ⟨sz qs aq (force Q P ((union_comm Q P).trans un) swap qx px ap),fun _ =>
       (H.mem_neighborFinset ..).mp (un ▸ mem_union_right P aq)⟩
  have empty : ¬C.Nonempty := fun ⟨t,tm⟩ => disjoint_left.mp pf.1 (force P Q un pf px qx aq tm)
    (force Q P ((union_comm Q P).trans un) swap qx px ap tm)
  exact ⟨by change C.card≤1; rw [not_nonempty_iff_eq_empty.mp empty,card_empty]; decide,fun h => (empty h).elim⟩

theorem pivot_contacts {e a b x : V} (ea : H.Adj e a) (eb : H.Adj e b) (ab : a≠b)
    (xe : ¬H.Adj x e) (xa : x≠a) (xb : x≠b) (xne : x≠e)
    (dx : H.degree x=4) (sx : trianglesAt H x=5)
    (rest : ∀ w,w≠e → 3≤H.degree w) (half : Fintype.card V≤2*gamma H) :
    ((additional H e a b).Nonempty → H.Adj x a ∨ H.Adj x b) ∧
    (2≤(additional H e a b).card → H.Adj x a ∧ H.Adj x b) := by
  have eq : additional H e b a=additional H e a b := by unfold additional; rw [inter_comm]
  constructor
  · intro c; by_cases h : H.Adj x b
    · exact Or.inr h
    · exact Or.inl ((missed H ea eb ab xe xa xb xne dx sx h rest half).2 c)
  · intro c
    constructor
    · by_contra no; have h := (missed H eb ea ab.symm xe xb xa xne dx sx no rest half).1
      rw [eq] at h; omega
    · by_contra no; have h := (missed H ea eb ab xe xa xb xne dx sx no rest half).1; omega

end Graffiti384b.EarCredit
#print axioms Graffiti384b.EarCredit.pivot_contacts
