import BicycleTripleCrossModel133
import BicycleThreeTrianglesCapsulesA133
import BicycleThreeTrianglesCapsulesB133
import ExteriorBowtie133
import BicycleTwoExteriorTriangles133

namespace Graffiti133ExteriorTriple
open SimpleGraph Graffiti133 Graffiti133Bicycle
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

def decodedPair (a : Fin 10) : Option (Fin 3×Fin 3) :=
  if h : a.val=0 then none else
    some (⟨(a.val-1)/3,by have := a.isLt; omega⟩,⟨(a.val-1)%3,by omega⟩)

def optionCode (x y : Option (Fin 3)) : Fin 10 :=
  match x,y with
  | some a,some b => slotCode a b
  | _,_ => 0

private theorem decoded_recovers :
    ∀ a : Fin 10, optionCode ((decodedPair a).map Prod.fst) ((decodedPair a).map Prod.snd)=a := by decide

def firstPort (x : Option (Fin 3)) : Option (Fin 3) := x.map (fun _=>0)

noncomputable def nextPort (x y : Option (Fin 3)) : Option (Fin 3) :=
  y.map (fun j => if ∃ i, x=some i ∧ i≠j then 1 else 0)

private theorem normalize_ports (x y : Option (Fin 3)) :
    ∃ p : Fin 3 ≃ Fin 3, (firstPort x).map p=x ∧ (nextPort x y).map p=y := by
  cases x with
  | none =>
    cases y with
    | none => exact ⟨Equiv.refl _,rfl,rfl⟩
    | some j =>
      exact ⟨Equiv.swap 0 j,rfl,by simp [nextPort]⟩
  | some i =>
    cases y with
    | none => exact ⟨Equiv.swap 0 i,by simp [firstPort],rfl⟩
    | some j =>
      fin_cases i <;> fin_cases j
      all_goals first
        | exact ⟨Equiv.refl _,by decide,by decide⟩
        | exact ⟨Equiv.swap 0 1,by decide,by decide⟩
        | exact ⟨Equiv.swap 0 2,by decide,by decide⟩
        | exact ⟨Equiv.swap 1 2,by decide,by decide⟩
        | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2),by decide,by decide⟩
        | exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1),by decide,by decide⟩

private theorem optional_slot_map_iff (p q : Fin 3 ≃ Fin 3) (A B : Option (Fin 3)) (i j : Fin 3) :
    optionCode (A.map p) (B.map q) = slotCode (p i) (q j) ↔ optionCode A B = slotCode i j := by
  by_cases an : A=none
  · subst A
    have zero (x y : Fin 3) : (0:Fin 10)≠slotCode x y := by
      intro e
      have ee := congrArg Fin.val e
      change 0=1+3*x.val+y.val at ee
      omega
    simp [optionCode,zero]
  · by_cases bn : B=none
    · subst B
      cases A with
      | none => contradiction
      | some a =>
        have zero (x y : Fin 3) : (0:Fin 10)≠slotCode x y := by
          intro e
          have ee := congrArg Fin.val e
          change 0=1+3*x.val+y.val at ee
          omega
        simp [optionCode,zero]
    · cases A with
      | none => contradiction
      | some a =>
        cases B with
        | none => contradiction
        | some b =>
          constructor
          · intro e
            obtain ⟨f,g⟩ := slotCode_injective (p a) (q b) (p i) (q j) e
            rw [show a=i from p.injective f,show b=j from q.injective g]
            rfl
          · intro e
            obtain ⟨rfl,rfl⟩ := slotCode_injective a b i j e
            rfl

def relabelSlots (p : Fin 3→Fin 3 ≃ Fin 3) (i : Fin 9) : Fin 9 :=
  ⟨3*(tripleGroup i).val+(p (tripleGroup i) (tripleSlot i)).val,by
    have := (tripleGroup i).isLt
    have := (p (tripleGroup i) (tripleSlot i)).isLt
    omega⟩

theorem relabel_group (p : Fin 3→Fin 3 ≃ Fin 3) (i : Fin 9) :
    tripleGroup (relabelSlots p i)=tripleGroup i := by
  apply Fin.ext
  have h := (p (tripleGroup i) (tripleSlot i)).isLt
  change (3*(tripleGroup i).val+(p (tripleGroup i) (tripleSlot i)).val)/3=(tripleGroup i).val
  omega

theorem relabel_slot (p : Fin 3→Fin 3 ≃ Fin 3) (i : Fin 9) :
    tripleSlot (relabelSlots p i)=p (tripleGroup i) (tripleSlot i) := by
  apply Fin.ext
  have h := (p (tripleGroup i) (tripleSlot i)).isLt
  change (3*(tripleGroup i).val+(p (tripleGroup i) (tripleSlot i)).val)%3=(p (tripleGroup i) (tripleSlot i)).val
  omega

theorem relabel_slots_inj (p : Fin 3→Fin 3 ≃ Fin 3) : Function.Injective (relabelSlots p) := by
  intro i j e
  have pg := congrArg tripleGroup e
  have ps := congrArg tripleSlot e
  rw [relabel_group,relabel_group] at pg
  rw [relabel_slot,relabel_slot,pg] at ps
  exact combined_slots_injective (Prod.ext pg ((p (tripleGroup j)).injective ps))

private theorem recode_first_first (x y : Option (Fin 3)) :
    (optionCode (firstPort x) (firstPort y)).val=0 ∨
      (optionCode (firstPort x) (firstPort y)).val=1 := by
  cases x <;> cases y <;> decide +revert

private theorem recode_next_first (x y z : Option (Fin 3)) :
    (optionCode (nextPort x y) (firstPort z)).val=0 ∨
    (optionCode (nextPort x y) (firstPort z)).val=1 ∨
    (optionCode (nextPort x y) (firstPort z)).val=4 := by
  cases y <;> cases z <;> simp [nextPort,firstPort,optionCode]
  split <;> decide

private theorem recode_next_next (x y z w : Option (Fin 3)) :
    (optionCode (nextPort x y) (nextPort z w)).val=0 ∨
    (optionCode (nextPort x y) (nextPort z w)).val=1 ∨
    (optionCode (nextPort x y) (nextPort z w)).val=2 ∨
    (optionCode (nextPort x y) (nextPort z w)).val=4 ∨
    (optionCode (nextPort x y) (nextPort z w)).val=5 := by
  cases y <;> cases w <;> simp [nextPort,optionCode]
  split <;> split <;> decide

theorem factor_three_triangle_normalization (a b c : Fin 10) :
    ∃ a' b' c' : Fin 10,
      (a'.val=0 ∨ a'.val=1) ∧ (b'.val=0 ∨ b'.val=1 ∨ b'.val=4) ∧
      (c'.val=0 ∨ c'.val=1 ∨ c'.val=2 ∨ c'.val=4 ∨ c'.val=5) ∧
      ∃ f : Fin 9→Fin 9, Function.Injective f ∧
        ∀ i j,tripleModel a b c (f i) (f j)=tripleModel a' b' c' i j := by
  let a0 := (decodedPair a).map Prod.fst
  let a1 := (decodedPair a).map Prod.snd
  let b0 := (decodedPair b).map Prod.fst
  let b2 := (decodedPair b).map Prod.snd
  let c1 := (decodedPair c).map Prod.fst
  let c2 := (decodedPair c).map Prod.snd
  obtain ⟨p,pA,pB⟩ := normalize_ports a0 b0
  obtain ⟨q,qA,qC⟩ := normalize_ports a1 c1
  obtain ⟨r,rB,rC⟩ := normalize_ports b2 c2
  let a' := optionCode (firstPort a0) (firstPort a1)
  let b' := optionCode (nextPort a0 b0) (firstPort b2)
  let c' := optionCode (nextPort a1 c1) (nextPort b2 c2)
  let slots : Fin 3→Fin 3 ≃ Fin 3 := ![p,q,r]
  have f1 (i j : Fin 3) : a=slotCode (p i) (q j) ↔ a'=slotCode i j := by
    simpa only [pA,qA,decoded_recovers,a0,a1,a'] using
      optional_slot_map_iff p q (firstPort a0) (firstPort a1) i j
  have f2 (i j : Fin 3) : b=slotCode (p i) (r j) ↔ b'=slotCode i j := by
    simpa only [pB,rB,decoded_recovers,b0,b2,b'] using
      optional_slot_map_iff p r (nextPort a0 b0) (firstPort b2) i j
  have f3 (i j : Fin 3) : c=slotCode (q i) (r j) ↔ c'=slotCode i j := by
    simpa only [qC,rC,decoded_recovers,c1,c2,c'] using
      optional_slot_map_iff q r (nextPort a1 c1) (nextPort b2 c2) i j
  refine ⟨a',b',c',recode_first_first _ _,recode_next_first _ _ _,recode_next_next _ _ _ _,
    relabelSlots slots,relabel_slots_inj slots,?_⟩
  have rows (g h i j : Fin 3) :
      modelPair a b c g h (slots g i) (slots h j)=modelPair a' b' c' g h i j := by
    fin_cases g <;> fin_cases h <;> simp [modelPair,slots,f1,f2,f3]
  intro i j
  unfold tripleModel
  rw [relabel_group,relabel_group,relabel_slot,relabel_slot]
  exact rows _ _ _ _

#print axioms factor_three_triangle_normalization
end Graffiti133ExteriorTriple


namespace Graffiti133ExteriorTriple
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def smallNormalizationTable : List ((Nat×Nat×Nat)×Nat) :=
  [((0,0,0),3050936352),
  ((0,0,1),731196385),
  ((0,0,2),731149729),
  ((0,0,4),731196321),
  ((0,0,5),731149665),
  ((0,1,0),1891861345),
  ((0,1,1),1888681442),
  ((0,1,2),1888681443),
  ((0,1,4),1854669218),
  ((0,1,5),1854669219),
  ((0,4,0),1891861281),
  ((0,4,1),1888634786),
  ((0,4,2),1888634787),
  ((0,4,4),1854622562),
  ((0,4,5),1854622563),
  ((1,0,0),3050936353),
  ((1,0,1),3049346402),
  ((1,0,2),3015334178),
  ((1,0,4),3049346403),
  ((1,0,5),3015334179),
  ((1,1,0),3050936354),
  ((1,1,1),3050936356),
  ((1,1,2),3050936357),
  ((1,1,4),1891861349),
  ((1,1,5),3050936358),
  ((1,4,0),3050936355),
  ((1,4,1),731196389),
  ((1,4,2),3015334182),
  ((1,4,4),1854622566),
  ((1,4,5),3050936359)]

def smallNormalization (a b c : Fin 10) : Nat :=
  (smallNormalizationTable.lookup (a.val,b.val,c.val)).getD 0

theorem complete_small_normalization (a b c : Fin 10)
    (ha : a.val=0 ∨ a.val=1) (hb : b.val=0 ∨ b.val=1 ∨ b.val=4)
    (hc : c.val=0 ∨ c.val=1 ∨ c.val=2 ∨ c.val=4 ∨ c.val=5) :
    normalizeOK a b c (smallNormalization a b c) := by
  have a' : a=0 ∨ a=1 := ha.imp Fin.ext Fin.ext
  have b' : b=0 ∨ b=1 ∨ b=4 := hb.imp Fin.ext (fun d=>d.imp Fin.ext Fin.ext)
  have c' : c=0 ∨ c=1 ∨ c=2 ∨ c=4 ∨ c=5 :=
    hc.imp Fin.ext (fun d=>d.imp Fin.ext (fun e=>e.imp Fin.ext (fun f=>f.imp Fin.ext Fin.ext)))
  rcases a' with rfl|rfl <;> rcases b' with rfl|rfl|rfl <;>
    rcases c' with rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms complete_small_normalization
end Graffiti133ExteriorTriple


namespace Graffiti133ExteriorTriple
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133Bicycle
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem no_three_disjoint_exterior_triangles
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (f : Fin 3→Fin 3→V)
    (fi : Function.Injective (fun p : Fin 3×Fin 3=>f p.1 p.2))
    (off : ∀ p i,Outside H.c (f p i))
    (clique : ∀ p i j,i≠j→G.Adj (f p i) (f p j)) : False := by
  obtain ⟨a,b,c,agree⟩ := extract_cross_model h4 f fi clique
  obtain ⟨a',b',c',ha,hb,hc,rel,relInj,relAdj⟩ := factor_three_triangle_normalization a b c
  let n := smallNormalization a' b' c'
  have ok : normalizeOK a' b' c' n := complete_small_normalization a' b' c' ha hb hc
  let q := permutationOfCode n
  let perm := rel ∘ q
  let g (i : Fin 9) := f (tripleGroup (perm i)) (tripleSlot (perm i))
  have gi : Function.Injective g := (fi.comp combined_slots_injective).comp (relInj.comp (fun i j h=>ok.1 i j h))
  have fo (i : Fin 9) : Outside H.c (g i) := off _ _
  have att (i : Fin 9) : ∃ k,∀ j,G.Adj (g i) (H.c j) ↔ k=j := by
    obtain ⟨k,h⟩ := site _ (fo i)
    exact ⟨k,fun j=>(h j).trans eq_comm⟩
  choose color contact using att
  generalize ge : shapeOfCode n = sh
  have shape (i j : Fin 9) : G.Adj (g i) (g j) ↔ bit (shapeRows sh) i.val j.val=true := by
    rw [←ge,ok.2,←relAdj]
    exact agree (perm i) (perm j)
  fin_cases sh
  · exact h9 (ThreeTrianglesNoCross.extension H h4 g gi fo color contact shape)
  · exact h9 (ThreeTrianglesOneCross.extension H h4 g gi fo color contact shape)
  · exact h9 (ThreeTrianglesTwoSame.extension H h4 g gi fo color contact shape)
  · exact h9 (ThreeTrianglesTwoDifferent.extension H h4 g gi fo color contact shape)
  · exact h9 (ThreeTrianglesThreeSSS.extension H h4 g gi fo color contact shape)
  · have a : G.Adj (g 0) (g 3) := (shape _ _).mpr (by decide)
    have b : G.Adj (g 7) (g 3) := (shape _ _).mpr (by decide)
    have c : G.Adj (g 0) (g 6) := (shape _ _).mpr (by decide)
    have d : G.Adj (g 7) (g 6) := (shape _ _).mpr (by decide)
    exact (by decide : (3:Fin 9)≠6) (gi (h4 _ _ _ _ (gi.ne (by decide)) a b c d))
  · exact h9 (ThreeTrianglesThreeSDD.extension H h4 g gi fo color contact shape)
  · exact h9 (ThreeTrianglesThreeDDD.extension H h4 g gi fo color contact shape)

#print axioms no_three_disjoint_exterior_triangles
end Graffiti133ExteriorTriple


namespace Graffiti133ExteriorTriple
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133TwoExteriorTriangles Graffiti133ExteriorBowtie
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem chosen_triangle_pair {O T : Finset V} (tr : TriangleIn G O T) (u : V) (um : u∈T) :
    ∃ a b,a∈O ∧ b∈O ∧ G.Adj u a ∧ G.Adj a b ∧ G.Adj b u ∧ T=insert u ({a,b}:Finset V) := by
  obtain ⟨a,b,c,am,bm,cm,ab,bc,ca,e⟩ := tr
  rw [←e] at um
  simp only [Finset.mem_insert,Finset.mem_singleton] at um
  rcases um with h|h|h <;> subst u
  · exact ⟨b,c,bm,cm,ab,bc,ca,e.symm⟩
  · exact ⟨c,a,cm,am,bc,ca,ab,by rw [←e]; ext x; simp [or_comm,or_left_comm]⟩
  · exact ⟨a,b,am,bm,ca,ab,bc,by rw [←e]; ext x; simp [or_comm,or_left_comm]⟩

theorem distinct_exterior_triangles_disjoint
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    {O T₁ T₂ : Finset V} (out : ∀ x∈O,Outside H.c x)
    (tr₁ : TriangleIn G O T₁) (tr₂ : TriangleIn G O T₂) (ne : T₁≠T₂) :
    Disjoint T₁ T₂ := by
  classical
  apply Finset.disjoint_left.mpr
  intro u um un
  obtain ⟨a,b,am,bm,ua,ab,bu,e1⟩ := chosen_triangle_pair tr₁ u um
  obtain ⟨c,d,cm,dm,uc,cd,du,e2⟩ := chosen_triangle_pair tr₂ u un
  have eq := exterior_triangles_sharing_hub_same_tips (G:=G) H h4 h9 site
    (out u (tr₁.subset um)) (out a am) (out b bm) (out c cm) (out d dm) ua ab bu uc cd du
  exact ne (by rw [e1,e2,eq])

private theorem vertices_of_triangle {O T : Finset V} (tr : TriangleIn G O T) :
    ∃ f : Fin 3→V, (∀ i,f i∈T) ∧ Function.Injective f ∧
      ∀ i j,i≠j→G.Adj (f i) (f j) := by
  classical
  let e : Fin 3 ≃ {x // x∈T} := (Fintype.equivFinOfCardEq
    ((Fintype.card_coe T).trans tr.card)).symm
  exact ⟨Subtype.val ∘ e,fun i=>(e i).property,Subtype.val_injective.comp e.injective,
    fun i j ne=>tr.clique _ _ (e i).property (e j).property (Subtype.val_injective.ne (e.injective.ne ne))⟩

theorem exterior_triangle_family_card_le_two
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (O : Finset V) (out : ∀ x∈O,Outside H.c x)
    (T : Finset (Finset V)) (mark : ∀ A∈T,TriangleIn G O A) : T.card≤2 := by
  classical
  by_contra! many
  obtain ⟨A,am⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have count := Finset.card_erase_add_one (s:=T) am
  obtain ⟨B,bm,C,cm,bc⟩ := Finset.one_lt_card.mp (show 1<(T.erase A).card by omega)
  have aB := (Finset.mem_erase.mp bm).1.symm
  have aC := (Finset.mem_erase.mp cm).1.symm
  let Q : Fin 3→Finset V := ![A,B,C]
  have distinct : Function.Injective Q := by
    apply List.nodup_ofFn.mp
    simpa [Q,List.ofFn_succ] using (show [A,B,C].Nodup by simp [aB,aC,bc])
  have membership (i : Fin 3) : Q i∈T := by
    fin_cases i
    · exact am
    · exact (Finset.mem_erase.mp bm).2
    · exact (Finset.mem_erase.mp cm).2
  have memberTri (i : Fin 3) : TriangleIn G O (Q i) := mark _ (membership i)
  choose f inside inj clique using fun i => vertices_of_triangle (memberTri i)
  have fi : Function.Injective (fun p : Fin 3×Fin 3=>f p.1 p.2) := by
    rintro ⟨p,i⟩ ⟨q,j⟩ he
    change f p i=f q j at he
    by_cases pq : p=q
    · subst q
      cases inj p he
      rfl
    · have dis := distinct_exterior_triangles_disjoint H h4 h9 site out
        (memberTri p) (memberTri q) (distinct.ne pq)
      exact (Finset.disjoint_left.mp dis (inside p i) (he.symm ▸ inside q j)).elim
  exact no_three_disjoint_exterior_triangles H h4 h9 site f fi
    (fun p i=>out _ ((memberTri p).subset (inside p i))) clique

theorem at_most_two_exterior_triangle_supports
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i)
    (O : Finset V) (out : ∀ x∈O,Outside H.c x) :
    ∃ T₁ T₂ : Finset V,T₁.card≤3 ∧ T₂.card≤3 ∧ AtMostTwo G O T₁ T₂ := by
  classical
  let T : Finset (Finset V) := Finset.univ.filter (TriangleIn G O)
  have mem (A : Finset V) : A∈T ↔ TriangleIn G O A := by simp [T]
  have bound := exterior_triangle_family_card_le_two H h4 h9 site O out T (fun A am=>(mem A).mp am)
  have cover (A B : Finset V) (sup : ∀ C∈T,C=A ∨ C=B) : AtMostTwo G O A B := by
    intro a b c am bm cm ab bc ca
    have tr : TriangleIn G O ({a,b,c}:Finset V) := ⟨a,b,c,am,bm,cm,ab,bc,ca,rfl⟩
    rcases sup _ ((mem _).mpr tr) with rfl|rfl
    · exact Or.inl Subset.rfl
    · exact Or.inr Subset.rfl
  by_cases none : T.Nonempty
  · obtain ⟨A,am⟩ := none
    have a3 := ((mem A).mp am).card
    by_cases rest : (T.erase A).Nonempty
    · obtain ⟨B,bm⟩ := rest
      have bT := (Finset.mem_erase.mp bm).2
      have b3 := ((mem B).mp bT).card
      refine ⟨A,B,by rw [a3],by rw [b3],cover A B ?_⟩
      intro C cm
      by_cases CA : C=A
      · exact Or.inl CA
      · refine Or.inr ?_
        by_contra CB
        have cards := Finset.card_erase_add_one (s:=T) am
        have ge := Finset.one_lt_card.mpr
          ⟨C,Finset.mem_erase.mpr ⟨CA,cm⟩,B,bm,CB⟩
        omega
    · refine ⟨A,∅,by rw [a3],by simp,cover A ∅ ?_⟩
      intro C cm
      refine Or.inl ?_
      by_contra CA
      exact rest ⟨C,Finset.mem_erase.mpr ⟨CA,cm⟩⟩
  · refine ⟨∅,∅,by simp,by simp,cover ∅ ∅ ?_⟩
    exact fun C cm=>(none ⟨C,cm⟩).elim

theorem singleton_seven_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x,Outside H.c x → ∃ i,∀ j,G.Adj x (H.c j) ↔ j=i) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let O : Finset V := Finset.univ \ Finset.univ.image H.c
  have out (x : V) (hx : x∈O) : Outside H.c x := by
    intro i e
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  obtain ⟨A,B,a,b,cover⟩ := at_most_two_exterior_triangle_supports H h4 h9 site O out
  exact singleton_seven_at_most_two_exterior_triangles_mean_four H h4 h9 site A B a b cover

#print axioms singleton_seven_mean_four
end Graffiti133ExteriorTriple
