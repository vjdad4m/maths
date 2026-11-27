import P8ModelLift133
import P8HeawoodCert

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133P8Heawood Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace Model
variable (M : Model G Graffiti133P8Heawood.Anchor)

def hasType (v : V) (t : Fin 4) : Prop :=
  M.Fresh v ∧ ∀ i, Profile t i = true ↔ G.Adj v (M.f i)

theorem classified {v : V} (off : M.Fresh v) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f)
    (adj : ∃ i, G.Adj v (M.f i)) : ∃ t, M.hasType v t := by
  obtain ⟨i,ei⟩ := adj
  let T := M.extend v off (M.contacts_true v)
  obtain ⟨t,ht⟩ := anchor_contacts (M.contacts v) (T.good h4 h5 h8) ⟨i,(M.contacts_true _ _).mpr ei⟩
  exact ⟨t,off,fun j => ht j ▸ M.contacts_true _ j⟩

theorem pair_rule {x y : V} {i j : Fin 4}
    (hx : M.hasType x i) (hy : M.hasType y j) (hne : x≠y)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) :
    AllowedPair i j (by classical exact decide (G.Adj y x)) := by
  classical
  let bit := decide (G.Adj y x)
  let T := M.extend x hx.1 hx.2
  have fresh : T.Fresh y := by
    intro k
    refine Fin.lastCases ?_ (fun a => ?_) k
    · simpa only [T,Model.extend_f_new] using hne.symm
    · simpa only [T,Model.extend_f_old] using hy.1 a
  have hits (k : Fin 10) : pairMask j bit k = true ↔ G.Adj y (T.f k) := by
    refine Fin.lastCases ?_ (fun a => ?_) k
    · simp only [T,Model.extend_f_new,pairMask_new,bit,decide_eq_true_eq]
    · simpa only [T,Model.extend_f_old,pairMask_old] using hy.2 a
  exact pair_contacts i j bit ((T.extend y fresh hits).good h4 h5 h8)

private def baseWitness (t : Fin 4) : Fin 9 := ![1,2,7,3] t
private def capA (t : Fin 4) : Fin 9 := ![0,1,0,2] t
private def capB (t : Fin 4) : Fin 9 := ![2,3,4,4] t
private lemma witness_cap : ∀ (t : Fin 4) (i : Fin 9),
    Graffiti133P8Heawood.Anchor (baseWitness t) i → i=capA t ∨ i=capB t := by decide
private lemma unique_witness : ∀ (i j : Fin 4), Profile j (baseWitness i)=true → i=j := by decide

theorem each_type (hm : ∀ x, 3≤localIndependence G x) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f)
    (i : Fin 4) : ∃ v, M.hasType v i := by
  obtain ⟨v,off,adj⟩ := M.exists_fresh_neighbor _ _ _ (witness_cap i) (hm _)
  obtain ⟨j,hj⟩ := M.classified off h4 h5 h8 ⟨baseWitness i,adj⟩
  exact ⟨v,(unique_witness i j ((hj.2 _).mpr adj)).symm ▸ hj⟩

private lemma different_patterns : ∀ i j : Fin 4,
    (∀ k, Profile i k = true ↔ Profile j k = true) → i=j := by decide

theorem type_inj {x : V} {i j : Fin 4} (hi : M.hasType x i) (hj : M.hasType x j) : i=j :=
  different_patterns _ _ (fun k => (hi.2 k).trans (hj.2 k).symm)

private lemma repetition : ∀ (i : Fin 4) (b : Bool), AllowedPair i i b → i=2 := by decide
private lemma diff_edges : ∀ (i j : Fin 4) (b : Bool), i≠j → AllowedPair i j b →
    (b=true ↔ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1)) := by decide

theorem type_adj {x y : V} {i j : Fin 4}
    (hx : M.hasType x i) (hy : M.hasType y j) (hne : i≠j)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) :
    G.Adj x y ↔ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) := by
  classical
  have hxy : x≠y := fun e => hne (M.type_inj hx (e.symm ▸ hy))
  have out := diff_edges i j _ hne (M.pair_rule hx hy hxy h4 h5 h8)
  simpa [G.adj_comm] using out

theorem type_unique {x y : V} {i : Fin 4}
    (hx : M.hasType x i) (hy : M.hasType y i) (w : V) (ht : M.hasType w 1)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) : x=y := by
  classical
  by_contra ne
  have eq : i=2 := repetition i _ (M.pair_rule hx hy ne h4 h5 h8)
  subst i
  have xw := (M.type_adj hx ht (by decide) h4 h5 h8).mpr (Or.inr ⟨rfl,rfl⟩)
  have yw := (M.type_adj hy ht (by decide) h4 h5 h8).mpr (Or.inr ⟨rfl,rfl⟩)
  have x7 := (hx.2 7).mp (by decide)
  have y7 := (hy.2 7).mp (by decide)
  exact ne (h4 (M.f 7) w x y (Ne.symm (ht.1 7)) x7.symm xw.symm y7.symm yw.symm)

private lemma core_old : ∀ i j : Fin 9, Core (i.castAdd 4) (j.castAdd 4) ↔ Graffiti133P8Heawood.Anchor i j := by decide
private lemma core_left : ∀ (i : Fin 9) (j : Fin 4), Core (i.castAdd 4) (j.natAdd 9) ↔ Profile j i=true := by decide
private lemma core_right : ∀ (i : Fin 4) (j : Fin 9), Core (i.natAdd 9) (j.castAdd 4) ↔ Profile i j=true := by decide
private lemma core_extra : ∀ i j : Fin 4, Core (i.natAdd 9) (j.natAdd 9) ↔
    (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) := by decide

def coreModel (v : Fin 4 → V) (hv : ∀ i, M.hasType (v i) i)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) :
    Model G Core where
  f := fun i => @Fin.addCases 9 4 (fun _ => V) M.f v i
  inj := by
    intro i j
    refine Fin.addCases (m:=9) (n:=4) ?_ ?_ i
    · intro i
      refine Fin.addCases (m:=9) (n:=4) ?_ ?_ j
      · intro j e
        exact congrArg (Fin.castAdd 4) (M.inj (by simpa using e))
      · intro j e
        exact ((hv j).1 i (by simpa using e.symm)).elim
    · intro i
      refine Fin.addCases (m:=9) (n:=4) ?_ ?_ j
      · intro j e
        exact ((hv i).1 j (by simpa using e)).elim
      · intro j e
        have eq : v i=v j := by simpa using e
        exact congrArg (Fin.natAdd 9) (M.type_inj (hv i) (eq.symm ▸ hv j))
  adj := by
    intro i j
    refine Fin.addCases (m:=9) (n:=4) ?_ ?_ i
    · intro i
      refine Fin.addCases (m:=9) (n:=4) ?_ ?_ j
      · intro j; simpa using (core_old i j).trans (M.adj i j)
      · intro j
        simpa only [Fin.addCases_left,Fin.addCases_right,G.adj_comm] using (core_left i j).trans ((hv j).2 i)
    · intro i
      refine Fin.addCases (m:=9) (n:=4) ?_ ?_ j
      · intro j; simpa using (core_right i j).trans ((hv i).2 j)
      · intro j
        by_cases hij : i=j
        · subst j
          simp only [Fin.addCases_right]
          exact iff_of_false (fun h => ((core_extra i i).mp h).elim
            (fun h => (show (1:Fin 4) ≠ 2 by decide) (h.1.symm.trans h.2))
            (fun h => (show (2:Fin 4) ≠ 1 by decide) (h.1.symm.trans h.2))) (G.loopless _)
        · simpa using (core_extra i j).trans (M.type_adj (hv i) (hv j) hij h4 h5 h8).symm

private lemma core_cap : ∀ j : Fin 13, Core 9 j → j=1 ∨ j=5 := by decide
private lemma model_eq : ∀ i j : Fin 14,
    Heawood i j ↔ ext Core (CoreMask FarProfile) i j := by decide

include M in
theorem extends_to_heawood (hm : ∀ x, 3 ≤ localIndependence G x)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (h8 : ¬∃ f : Fin 8 → V, InducedPath G f) :
    Nonempty (Model G Heawood) := by
  classical
  choose v hv using M.each_type hm h4 h5 h8
  let C := M.coreModel v hv h4 h5 h8
  obtain ⟨x,hx,ex⟩ := C.exists_fresh_neighbor 9 1 5 core_cap (hm _)
  have noAnchor (i : Fin 9) : ¬G.Adj x (M.f i) := by
    intro e
    have off (j : Fin 9) : x ≠ M.f j := by simpa [C,coreModel] using hx (j.castAdd 4)
    obtain ⟨t,ht⟩ := M.classified off h4 h5 h8 ⟨i,e⟩
    have same := M.type_unique ht (hv t) (v 1) (hv 1) h4 h5 h8
    exact hx (t.natAdd 9) (by simpa [C,coreModel] using same)
  let bits (i : Fin 4) := decide (G.Adj x (v i))
  have bg : ∃ i,bits i=true := by
    refine ⟨0,?_⟩
    change G.Adj x (C.f ((0:Fin 4).natAdd 9)) at ex
    simpa only [bits,decide_eq_true_eq,C,coreModel,Fin.addCases_right] using ex
  have oldMask : ∀ (b : Fin 4 → Bool) (i : Fin 9), CoreMask b (i.castAdd 4) = false := by
    intro b i
    have h : ¬9≤(i.castAdd 4).val := Nat.not_le_of_lt i.isLt
    simp [CoreMask,h]
  have newMask : ∀ (b : Fin 4 → Bool) (i : Fin 4), CoreMask b (i.natAdd 9) = b i := by
    intro b i
    have h : 9≤(i.natAdd 9).val := by simp
    simp only [CoreMask,dif_pos h]
    congr 1
    apply Fin.ext
    change 9+i.val-9=i.val
    omega
  have bOK (i : Fin 13) : CoreMask bits i=true ↔ G.Adj x (C.f i) := by
    refine Fin.addCases (m:=9) (n:=4) ?_ ?_ i
    · intro i; simp [oldMask,C,coreModel,noAnchor]
    · intro i; simp [newMask,bits,C,coreModel]
  have fact := core_contacts bits ((C.extend x hx bOK).good h4 h5 h8) bg
  have maskEq : bits=FarProfile := funext fact
  have proof (i : Fin 13) : CoreMask FarProfile i=true ↔ G.Adj x (C.f i) := maskEq ▸ bOK i
  exact ⟨(C.extend x hx proof).changeRel model_eq⟩

#print axioms extends_to_heawood
end Model
end Graffiti133Eighth
