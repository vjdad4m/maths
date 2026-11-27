import ThetaSevenFaithfulSplice
import EarCase

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulCap
open SquareCap (SmallTrivial FactorOn omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open ThetaSevenFaithfulSplice (Dead Live Faith put)
open ThetaSevenFaithfulRefill (In Shape)
noncomputable section
universe u

variable {V : Type u} {I : Type*}

/-- Attachment allowing the same genuine outside port to have two
wires to two different internal vertices. -/
def link? (p : Port↪V) (wire : Port→I→Bool) (x : V) (j : I) : Prop :=
  ∃ k : Port,p k=x ∧ wire k j=true

instance [DecidableEq V] (p : Port↪V) (wire : Port→I→Bool) (x : V) (j : I) :
    Decidable (link? p wire x j) :=
  inferInstanceAs (Decidable (∃ k : Port,p k=x ∧ wire k j=true))

def relation (B : SimpleGraph V) (K : SimpleGraph I) (p : Port↪V)
    (wire : Port→I→Bool) : V⊕I→V⊕I→Prop
  | .inl x,.inl y => B.Adj x y
  | .inr x,.inr y => K.Adj x y
  | .inl x,.inr y => link? p wire x y
  | .inr y,.inl x => link? p wire x y

def glue (B : SimpleGraph V) (K : SimpleGraph I) (p : Port↪V)
    (wire : Port→I→Bool) : SimpleGraph (V⊕I) where
  Adj := relation B K p wire
  symm := by
    intro x y e
    cases x <;> cases y
    · exact B.symm e
    · exact e
    · exact e
    · exact K.symm e
  loopless := by
    intro x e
    cases x
    · exact B.loopless _ e
    · exact K.loopless _ e

instance [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj]
    (K : SimpleGraph I) [DecidableRel K.Adj] (p : Port↪V) (wire : Port→I→Bool) :
    DecidableRel (glue B K p wire).Adj := by
  intro x y
  cases x <;> cases y
  · exact inferInstanceAs (Decidable (B.Adj _ _))
  · exact inferInstanceAs (Decidable (link? p wire _ _))
  · exact inferInstanceAs (Decidable (link? p wire _ _))
  · exact inferInstanceAs (Decidable (K.Adj _ _))

private def leftMap (B : SimpleGraph V) (K : SimpleGraph I) (p : Port↪V)
    (wire : Port→I→Bool) (x : V) :
    B.neighborSet x ⊕ {j : I // link? p wire x j} → (glue B K p wire).neighborSet (.inl x)
  | .inl n => ⟨.inl n.val,n.property⟩
  | .inr n => ⟨.inr n.val,n.property⟩

private theorem left_bij (B : SimpleGraph V) (K : SimpleGraph I) (p : Port↪V)
    (wire : Port→I→Bool) (x : V) : Function.Bijective (leftMap B K p wire x) := by
  constructor
  · intro a b e
    have h := congrArg Subtype.val e
    cases a <;> cases b
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective h))
    · exact Sum.noConfusion h
    · exact Sum.noConfusion h
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr_injective h))
  · rintro ⟨q,hq⟩
    cases q with
    | inl v => exact ⟨.inl ⟨v,hq⟩,rfl⟩
    | inr j => exact ⟨.inr ⟨j,hq⟩,rfl⟩

private def rightMap (B : SimpleGraph V) (K : SimpleGraph I) (p : Port↪V)
    (wire : Port→I→Bool) (x : I) :
    {i : Port // wire i x=true} ⊕ K.neighborSet x → (glue B K p wire).neighborSet (.inr x)
  | .inl n => ⟨.inl (p n.val),⟨n.val,rfl,n.property⟩⟩
  | .inr n => ⟨.inr n.val,n.property⟩

private theorem right_bij (B : SimpleGraph V) (K : SimpleGraph I) (p : Port↪V)
    (wire : Port→I→Bool) (x : I) : Function.Bijective (rightMap B K p wire x) := by
  constructor
  · intro a b e
    have h := congrArg Subtype.val e
    cases a <;> cases b
    · exact congrArg Sum.inl (Subtype.ext (p.injective (Sum.inl_injective h)))
    · exact Sum.noConfusion h
    · exact Sum.noConfusion h
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr_injective h))
  · rintro ⟨z,h⟩
    cases z with
    | inl v =>
      obtain ⟨i,pv,ed⟩ : link? p wire v x := h
      exact ⟨.inl ⟨i,ed⟩,Subtype.ext (congrArg Sum.inl pv)⟩
    | inr j => exact ⟨.inr ⟨j,h⟩,rfl⟩

private theorem ext_degree [Fintype V] [Fintype I] [DecidableEq V]
    (B : SimpleGraph V) [DecidableRel B.Adj]
    (K : SimpleGraph I) [DecidableRel K.Adj] (p : Port↪V) (wire : Port→I→Bool) (x : V) :
    (glue B K p wire).degree (Sum.inl x)=
      B.degree x+((univ : Finset I).filter (link? p wire x)).card := by
  classical
  rw [←card_neighborSet_eq_degree]
  rw [←Fintype.card_congr (Equiv.ofBijective _ (left_bij B K p wire x))]
  rw [Fintype.card_sum,card_neighborSet_eq_degree,Fintype.card_subtype]

private theorem in_degree [Fintype V] [Fintype I] [DecidableEq V]
    (B : SimpleGraph V) [DecidableRel B.Adj]
    (K : SimpleGraph I) [DecidableRel K.Adj] (p : Port↪V) (wire : Port→I→Bool) (x : I) :
    (glue B K p wire).degree (Sum.inr x)=
      ((univ : Finset Port).filter (fun i=>wire i x=true)).card + K.degree x := by
  classical
  rw [←card_neighborSet_eq_degree]
  rw [←Fintype.card_congr (Equiv.ofBijective _ (right_bij B K p wire x))]
  rw [Fintype.card_sum,card_neighborSet_eq_degree,Fintype.card_subtype]

def edges9 : List (Fin 9×Fin 9) :=
  [(0,1),(0,5),(0,6),(1,2),(2,3),(3,4),(3,6),(4,5),(1,7),(7,8)]

def edges3 : List (Fin 3×Fin 3) := [(0,1)]

private def fileGraph {α : Type*} (E : List (α×α)) (nd : ∀ a,(a,a)∉E) : SimpleGraph α where
  Adj a b := (a,b)∈E∨(b,a)∈E
  symm := fun _ _ h=>h.elim Or.inr Or.inl
  loopless _ h:= nd _ (h.elim id id)

def core9 := fileGraph edges9 (by decide)
def core3 := fileGraph edges3 (by decide)

instance : DecidableRel core9.Adj :=
  fun x y=>inferInstanceAs (Decidable ((x,y)∈edges9∨(y,x)∈edges9))
instance : DecidableRel core3.Adj :=
  fun x y=>inferInstanceAs (Decidable ((x,y)∈edges3∨(y,x)∈edges3))

/-- Ports in order: original p1,p2,p3,p4, then the other neighbor
of the absorbed original p0. Sites7,8 are the absorbed pair. -/
def wire9 (p : Port) (i : Fin 9) : Bool :=
  decide ((p,i)∈([(0,2),(0,8),(1,4),(2,6),(2,8),(3,5),(4,7)] : List (Port×Fin 9)))

def wire3 (p : Port) (i : Fin 3) : Bool :=
  decide ((p,i)∈([(0,1),(0,2),(1,2),(2,0),(2,2),(3,1),(4,0)] : List (Port×Fin 3)))

def ambient (B : SimpleGraph V) (p : Port↪V) := glue B core9 p wire9

def candidate (B : SimpleGraph V) (p : Port↪V) := glue B core3 p wire3

instance [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (p : Port↪V) :
    DecidableRel (ambient B p).Adj :=
  inferInstanceAs (DecidableRel (glue B core9 p wire9).Adj)

instance [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (p : Port↪V) :
    DecidableRel (candidate B p).Adj :=
  inferInstanceAs (DecidableRel (glue B core3 p wire3).Adj)

def target (B : SimpleGraph V) (p : Port↪V) :=
  omitEdge (ambient B p) (In 7) (In 8)

def restricted (B : SimpleGraph V) (p : Port↪V) :=
  omitEdge (candidate B p) Faith (.inl (p 1))

private theorem wire_total : ∀ i : Port,
    ((univ : Finset (Fin 3)).filter (fun x=>wire3 i x=true)).card =
    ((univ : Finset (Fin 9)).filter (fun x=>wire9 i x=true)).card := by decide

private theorem equal_ext [DecidableEq V] (p : Port↪V) (v : V) :
    ((univ : Finset (Fin 3)).filter (link? p wire3 v)).card =
    ((univ : Finset (Fin 9)).filter (link? p wire9 v)).card := by
  by_cases h : ∃ i : Port,p i=v
  · obtain ⟨j,rfl⟩ := h
    have eq {S : Type} (w : Port→S→Bool) (x : S) :
        link? p w (p j) x ↔ w j x=true := by
      constructor
      · rintro ⟨i,h,hi⟩
        exact (p.injective h) ▸ hi
      · intro h
        exact ⟨j,rfl,h⟩
    have ain : ((univ : Finset (Fin 3)).filter (link? p wire3 (p j))) =
        univ.filter (fun x=>wire3 j x=true) := by
      ext x
      simp only [mem_filter,mem_univ,true_and]
      exact eq wire3 x
    have aout : ((univ : Finset (Fin 9)).filter (link? p wire9 (p j))) =
        univ.filter (fun x=>wire9 j x=true) := by
      ext x
      simp only [mem_filter,mem_univ,true_and]
      exact eq wire9 x
    rw [ain,aout]
    exact wire_total j
  · have none {S : Type} (w : Port→S→Bool) (x : S) : ¬link? p w v x :=
      fun ⟨i,e,_⟩=>h ⟨i,e⟩
    have empty {S : Type} [Fintype S] (w : Port→S→Bool) :
        ((univ : Finset S).filter (link? p w v))=∅ := by
      ext x
      simp only [mem_filter,mem_univ,true_and,not_mem_empty,iff_false]
      exact none w x
    simp [empty wire3,empty wire9]

variable [Fintype V] [DecidableEq V]

/-- The degree transfer allows two wires at ports p1,p3 without
double-counting, since they lead to distinct internal vertices. -/
theorem candidate_cubic (B : SimpleGraph V) [DecidableRel B.Adj] (p : Port↪V)
    (cub : ∀ x,(ambient B p).degree x=3) : ∀ x,(candidate B p).degree x=3 := by
  intro x
  cases x with
  | inl v =>
    have orig := cub (Sum.inl v)
    change (glue B core9 p wire9).degree (Sum.inl v)=3 at orig
    rw [ext_degree] at orig
    change (glue B core3 p wire3).degree (Sum.inl v)=3
    rw [ext_degree,equal_ext]
    exact orig
  | inr j =>
    change (glue B core3 p wire3).degree (Sum.inr j)=3
    rw [in_degree]
    exact (by decide : ∀ j : Fin 3,
      ((univ : Finset Port).filter (fun i=>wire3 i j=true)).card+core3.degree j=3) j

/-- Exact graph transfer from this specific seven-wire cap. -/
theorem lift (B : SimpleGraph V) (p : Port↪V)
    (f : FactorOn (restricted B p) (univ.erase Dead)) :
    FactorOn (target B p) (univ.erase (In 6)) := by
  have kept (x y : Fin 9) (xy : core9.Adj x y)
      (d : ¬((x=7∧y=8)∨(x=8∧y=7))) : (target B p).Adj (In x) (In y) :=
    ⟨xy,by simpa using d⟩
  have sh : Shape (target B p) := {
    e01 := kept 0 1 (by decide) (by decide)
    e12 := kept 1 2 (by decide) (by decide)
    e23 := kept 2 3 (by decide) (by decide)
    e34 := kept 3 4 (by decide) (by decide)
    e45 := kept 4 5 (by decide) (by decide)
    e50 := kept 5 0 (by decide) (by decide)
    e17 := kept 1 7 (by decide) (by decide) }
  have q2 : (target B p).Adj (In 2) (.inl (p 0)) := ⟨⟨0,rfl,by decide⟩,by simp⟩
  have q5 : (target B p).Adj (In 5) (.inl (p 3)) := ⟨⟨3,rfl,by decide⟩,by simp⟩
  refine ThetaSevenFaithfulSplice.splice (fun h=>(by decide : (0:Port)≠3)
    (p.injective h)) sh q2 q5 ?_ ?_ f
  · intro x nd h
    cases x with
    | inl y =>
      obtain ⟨i,e,edge⟩ : link? p wire3 y 1 := h.1
      have al : ∀ i : Port,wire3 i 1=true→i=0∨i=3 := by decide
      rcases al i edge with rfl|rfl
      · exact Or.inl (congrArg Sum.inl e.symm)
      · exact Or.inr (congrArg Sum.inl e.symm)
    | inr j =>
      have x : core3.Adj 1 j := h.1
      have only : ∀ j : Fin 3,core3.Adj 1 j→j=0 := by decide
      exact (nd (congrArg Sum.inr (only j x))).elim
  · have tag : ∀ i : Fin 3,i≠0→i≠1→i=2 := by decide
    have fa (y : V) (e : (restricted B p).Adj Faith (.inl y)) :
        (target B p).Adj (In 8) (.inl y) := by
      obtain ⟨i,eq,run⟩ : link? p wire3 y 2 := e.1
      have only : ∀ i : Port,wire3 i 2=true→i=0∨i=1∨i=2 := by decide
      rcases only i run with rfl|rfl|rfl
      · exact ⟨⟨0,eq,by decide⟩,by simp⟩
      · exact (e.2 (Or.inl ⟨rfl,congrArg Sum.inl eq.symm⟩)).elim
      · exact ⟨⟨2,eq,by decide⟩,by simp⟩
    intro x y xd xl yd yl e
    cases x with
    | inl u =>
      cases y with
      | inl v => exact ⟨e.1,by simp⟩
      | inr j =>
        have h := tag j (fun z=>yd (congrArg Sum.inr z)) (fun z=>yl (congrArg Sum.inr z))
        subst j
        exact (fa u e.symm).symm
    | inr i =>
      have hi := tag i (fun z=>xd (congrArg Sum.inr z)) (fun z=>xl (congrArg Sum.inr z))
      subst i
      cases y with
      | inl v => exact fa v e
      | inr j =>
        have hj := tag j (fun z=>yd (congrArg Sum.inr z)) (fun z=>yl (congrArg Sum.inr z))
        subst j
        exact (e.ne rfl).elim

/-- This three-vertex cap is six vertices smaller than the enlarged
theta. Once the cap is cyclic-four, the only premise is smaller F2. -/
theorem reduce
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {p : Port↪V}
    (cub : ∀ v,(ambient B p).degree v=3)
    (valid : SmallTrivial (candidate B p)) (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) := by
  let C := candidate B p
  have cc : ∀ v,C.degree v=3 := candidate_cubic B p cub
  have big : 5≤Fintype.card V := by simpa using (Fintype.card_le_of_injective p p.injective)
  have c3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have c9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  have conn := three_connected_of_small_trivial C cc (by omega) valid
  have wire : C.Adj Faith (Sum.inl (p 1)) := ⟨1,rfl,by decide⟩
  have f := smaller (V⊕Fin 3) C (by omega) cc conn valid (by omega)
    Dead Faith (Sum.inl (p 1)) wire
  exact lift B p f

#print axioms candidate_cubic
#print axioms lift
#print axioms reduce
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulCap
