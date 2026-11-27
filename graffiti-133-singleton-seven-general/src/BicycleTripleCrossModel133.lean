import BicycleShapeCheck133

namespace Graffiti133ExteriorTriple
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

private theorem third_slot (a b : Fin 3) :
    ∃ c : Fin 3,c≠a ∧ c≠b := by decide +revert

theorem single_cross_edge (h4 : FourCycleFree G) {f g : Fin 3→V}
    (fInj : Function.Injective f) (gInj : Function.Injective g)
    (sep : ∀ i j,f i≠g j)
    (fc : ∀ i j,i≠j→G.Adj (f i) (f j))
    (gc : ∀ i j,i≠j→G.Adj (g i) (g j))
    (a b c d : Fin 3) (ab : G.Adj (f a) (g b)) (cd : G.Adj (f c) (g d)) :
    a=c ∧ b=d := by
  by_cases ac : a=c
  · subst c
    refine ⟨rfl,?_⟩
    by_contra bd
    obtain ⟨e,eb,ed⟩ := third_slot b d
    exact sep a e (h4 _ _ _ _ (gInj.ne bd) ab.symm cd.symm (gc _ _ eb.symm) (gc _ _ ed.symm))
  · by_cases bd : b=d
    · subst d
      obtain ⟨e,ea,ec⟩ := third_slot a c
      exact (sep e b (h4 _ _ _ _ (fInj.ne ac) ab cd (fc _ _ ea.symm) (fc _ _ ec.symm)).symm).elim
    · exact (sep c b (h4 _ _ _ _ (sep a d)
        (fc _ _ ac) cd.symm ab (gc _ _ (fun e=>bd e.symm)))).elim

def slotCode (a b : Fin 3) : Fin 10 := ⟨1+3*a.val+b.val,by
  have := a.isLt
  have := b.isLt
  omega⟩

theorem slotCode_injective (a b c d : Fin 3) (eq : slotCode a b=slotCode c d) :
    a=c ∧ b=d := by
  have e := congrArg Fin.val eq
  change 1+3*a.val+b.val=1+3*c.val+d.val at e
  have := b.isLt
  have := d.isLt
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

theorem exactly_one_cross_code (h4 : FourCycleFree G) {f g : Fin 3→V}
    (fi : Function.Injective f) (gi : Function.Injective g)
    (sep : ∀ i j,f i≠g j)
    (fc : ∀ i j,i≠j→G.Adj (f i) (f j))
    (gc : ∀ i j,i≠j→G.Adj (g i) (g j)) :
    ∃ code : Fin 10, ∀ a b,G.Adj (f a) (g b) ↔ code=slotCode a b := by
  by_cases pos : ∃ a b,G.Adj (f a) (g b)
  · obtain ⟨a,b,ab⟩ := pos
    refine ⟨slotCode a b,?_⟩
    intro c d
    constructor
    · intro cd
      obtain ⟨ac,bd⟩ := single_cross_edge h4 fi gi sep fc gc a b c d ab cd
      rw [ac,bd]
    · intro eq
      obtain ⟨rfl,rfl⟩ := slotCode_injective a b c d eq
      exact ab
  · refine ⟨0,?_⟩
    intro a b
    refine ⟨fun e=>(pos ⟨a,b,e⟩).elim,?_⟩
    intro e
    have v := congrArg Fin.val e
    change 0=1+3*a.val+b.val at v
    omega

#print axioms exactly_one_cross_code
end Graffiti133ExteriorTriple


namespace Graffiti133ExteriorTriple
open SimpleGraph Graffiti133 Graffiti133Bicycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def tripleGroup (i : Fin 9) : Fin 3 := ⟨i.val/3,by have := i.isLt; omega⟩
def tripleSlot (i : Fin 9) : Fin 3 := ⟨i.val%3,by omega⟩

theorem combined_slots_injective : Function.Injective (fun i=> (tripleGroup i,tripleSlot i)) := by
  intro i j e
  have q := congrArg (fun a : Fin 3 × Fin 3=>a.1.val) e
  have r := congrArg (fun a : Fin 3 × Fin 3=>a.2.val) e
  change i.val/3=j.val/3 at q
  change i.val%3=j.val%3 at r
  exact Fin.ext (by omega)

def modelPair (a b c : Fin 10) (p q x y : Fin 3) : Bool :=
  if p=q then decide (x≠y) else
  match p.val,q.val with
  | 0,1 => decide (a=slotCode x y)
  | 1,0 => decide (a=slotCode y x)
  | 0,2 => decide (b=slotCode x y)
  | 2,0 => decide (b=slotCode y x)
  | 1,2 => decide (c=slotCode x y)
  | 2,1 => decide (c=slotCode y x)
  | _,_ => false

def tripleModel (a b c : Fin 10) (i j : Fin 9) : Bool :=
  modelPair a b c (tripleGroup i) (tripleGroup j) (tripleSlot i) (tripleSlot j)

def shapeRows (i : Fin 8) : List Nat :=
  ([[6,5,3,48,40,24,384,320,192],[14,5,3,49,40,24,384,320,192],[78,5,3,49,40,24,385,320,192],[14,69,3,49,40,24,386,320,192],[78,5,3,113,40,24,393,320,192],[78,5,3,177,40,24,385,328,192],[78,5,3,49,168,24,385,336,192],[14,69,3,49,168,24,386,336,192]] : List (List Nat)).getD i.val []

def shapeOfCode (n : Nat) : Fin 8 := ⟨n%8,by omega⟩
def permutationOfCode (n : Nat) (i : Fin 9) : Fin 9 :=
  ⟨(n/8/9^i.val)%9,by omega⟩

def normalizeOK (a b c : Fin 10) (n : Nat) : Prop :=
  (∀ i j : Fin 9, permutationOfCode n i = permutationOfCode n j → i=j) ∧
  ∀ i j : Fin 9, bit (shapeRows (shapeOfCode n)) i.val j.val =
    tripleModel a b c (permutationOfCode n i) (permutationOfCode n j)

instance (a b c : Fin 10) (n : Nat) : Decidable (normalizeOK a b c n) := by
  unfold normalizeOK
  infer_instance

end Graffiti133ExteriorTriple


namespace Graffiti133ExteriorTriple
open SimpleGraph Graffiti133 Graffiti133Bicycle
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} {G : SimpleGraph V}

theorem extract_cross_model (h4 : FourCycleFree G)
    (f : Fin 3→Fin 3→V)
    (fi : Function.Injective (fun p : Fin 3×Fin 3=>f p.1 p.2))
    (clique : ∀ p i j,i≠j→G.Adj (f p i) (f p j)) :
    ∃ a b c : Fin 10, ∀ i j : Fin 9,
      G.Adj (f (tripleGroup i) (tripleSlot i)) (f (tripleGroup j) (tripleSlot j)) ↔
        tripleModel a b c i j=true := by
  have fi' (p : Fin 3) : Function.Injective (f p) := by
    intro i j e
    have h : (p,i)=(p,j) := fi e
    exact congrArg Prod.snd h
  have apart (p q : Fin 3) (pq : p≠q) (i j : Fin 3) : f p i≠f q j :=
    fun he=>pq (congrArg Prod.fst (show (p,i)=(q,j) from fi he))
  obtain ⟨a,ha⟩ := exactly_one_cross_code h4 (fi' 0) (fi' 1) (apart _ _ (by decide)) (clique 0) (clique 1)
  obtain ⟨b,hb⟩ := exactly_one_cross_code h4 (fi' 0) (fi' 2) (apart _ _ (by decide)) (clique 0) (clique 2)
  obtain ⟨c,hc⟩ := exactly_one_cross_code h4 (fi' 1) (fi' 2) (apart _ _ (by decide)) (clique 1) (clique 2)
  have atSame (p i j : Fin 3) : G.Adj (f p i) (f p j) ↔ i≠j :=
    ⟨fun ee ij=>ee.ne (congrArg (f p) ij),clique p i j⟩
  have ea (i j : Fin 3) : G.Adj (f 1 i) (f 0 j) ↔ a=slotCode j i :=
    (G.adj_comm _ _).trans (ha j i)
  have eb (i j : Fin 3) : G.Adj (f 2 i) (f 0 j) ↔ b=slotCode j i :=
    (G.adj_comm _ _).trans (hb j i)
  have ec (i j : Fin 3) : G.Adj (f 2 i) (f 1 j) ↔ c=slotCode j i :=
    (G.adj_comm _ _).trans (hc j i)
  have general (p q i j : Fin 3) :
      G.Adj (f p i) (f q j) ↔ modelPair a b c p q i j=true := by
    fin_cases p <;> fin_cases q
    · simpa [modelPair] using atSame 0 i j
    · simpa [modelPair] using ha i j
    · simpa [modelPair] using hb i j
    · simpa [modelPair] using ea i j
    · simpa [modelPair] using atSame 1 i j
    · simpa [modelPair] using hc i j
    · simpa [modelPair] using eb i j
    · simpa [modelPair] using ec i j
    · simpa [modelPair] using atSame 2 i j
  exact ⟨a,b,c,fun i j=>general (tripleGroup i) (tripleGroup j) (tripleSlot i) (tripleSlot j)⟩

#print axioms extract_cross_model
end Graffiti133ExteriorTriple
