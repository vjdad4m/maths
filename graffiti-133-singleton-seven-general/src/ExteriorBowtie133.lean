import NoFiveHoles133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133ExteriorBowtie
open SimpleGraph Finset Graffiti133 Graffiti133NoFive
set_option maxHeartbeats 10000000
set_option maxRecDepth 15000
set_option linter.unusedSectionVars false

def bowtie (i j : Fin 5) : Prop :=
  (i=0 ∧ j≠0) ∨ (j=0 ∧ i≠0) ∨
  (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=3)
instance : DecidableRel bowtie := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private def BRel (c : Fin 5 → Fin 7) (i j : Fin 12) : Prop :=
  if hi : i.val < 7 then
    if hj : j.val < 7 then Cyclic ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else c ⟨j.val-7,by have := j.isLt; omega⟩=⟨i.val,hi⟩
  else if hj : j.val < 7 then c ⟨i.val-7,by have := i.isLt; omega⟩=⟨j.val,hj⟩
  else bowtie ⟨i.val-7,by have := i.isLt; omega⟩ ⟨j.val-7,by have := j.isLt; omega⟩
instance (c : Fin 5 → Fin 7) : DecidableRel (BRel c) := by
  intro i j
  unfold BRel
  split <;> split <;> infer_instance

private def middle (i : Fin 7) : Prop := 2 ≤ i.val ∧ i.val ≤ 5
private instance : DecidablePred middle := fun _ => inferInstanceAs (Decidable (_ ∧ _))
private def norm (a b c d : Fin 7) : Prop :=
  middle a ∧ middle b ∧ middle c ∧ middle d ∧
  a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d ∧ ¬Cyclic a b ∧ ¬Cyclic c d
private instance (a b c d : Fin 7) : Decidable (norm a b c d) := by unfold norm; infer_instance

private def witness (a b c d : Fin 7) : Fin 9 → Fin 12 :=
  match a.val,b.val,c.val,d.val with
  | 2, 4, 3, 5 => ![0,1,2,8,9,4,5,11,10]
  | 2, 4, 5, 3 => ![0,1,2,8,9,4,5,10,11]
  | 3, 5, 2, 4 => ![0,1,2,10,11,4,5,9,8]
  | 3, 5, 4, 2 => ![0,1,2,11,10,4,5,9,8]
  | 4, 2, 3, 5 => ![0,1,2,9,8,4,5,11,10]
  | 4, 2, 5, 3 => ![0,1,2,9,8,4,5,10,11]
  | 5, 3, 2, 4 => ![0,1,2,10,11,4,5,8,9]
  | 5, 3, 4, 2 => ![0,1,2,11,10,4,5,8,9]
  | _, _, _, _ => ![0,0,0,0,0,0,0,0,0]

private lemma certificate : ∀ a b c d, norm a b c d →
    let p := witness a b c d
    (∀ i j, p i=p j → i=j) ∧ ∀ i j, i < j →
      (BRel ![0,a,b,c,d] (p i) (p j) ↔ i.val+1=j.val) := by decide

private lemma rot_inj : ∀ r i j : Fin 7, i+r=j+r → i=j := by decide
private lemma rot_sur : ∀ r j : Fin 7, ∃ i, i+r=j := by decide
private lemma rot_cyc : ∀ r i j : Fin 7, Cyclic (i+r) (j+r) ↔ Cyclic i j := by decide
private lemma rootMiddle : ∀ i : Fin 7, i≠0 → ¬Cyclic 0 i → middle i := by decide
private def partner : Fin 5 → Fin 5 := ![0,2,1,4,3]
private lemma bow_from_root : ∀ i : Fin 5, i≠0 → bowtie i 0 := by decide
private lemma bow_partner : ∀ i : Fin 5, i≠0 → bowtie 0 (partner i) ∧ bowtie i (partner i) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem lift_model (H : Hole G 7) (f : Fin 5 → V) (fi : Function.Injective f)
    (off : ∀ i, Outside H.c (f i)) (shape : ∀ i j,G.Adj (f i) (f j) ↔ bowtie i j)
    (q : Fin 5 → Fin 7) (contact : ∀ i j,G.Adj (f i) (H.c j) ↔ j=q i) :
    ∃ F : Fin 12 → V, Function.Injective F ∧ (∀ i j,G.Adj (F i) (F j) ↔ BRel q i j) := by
  let old (i : Fin 7) : Fin 12 := Fin.castLE (by decide) i
  let new (i : Fin 5) : Fin 12 := ⟨i.val+7,by have := i.isLt; omega⟩
  let F (i : Fin 12) := if hi : i.val < 7 then H.c ⟨i.val,hi⟩ else f ⟨i.val-7,by have := i.isLt; omega⟩
  have vOld (i : Fin 7) : F (old i)=H.c i := by simp [F,old,i.isLt]
  have vNew (i : Fin 5) : F (new i)=f i := by
    have ge : ¬i.val+7 < 7 := by omega
    simp [F,new,ge]
  have elk (i : Fin 12) : (∃ j, i=old j) ∨ ∃ j, i=new j := by
    by_cases hi : i.val < 7
    · exact Or.inl ⟨⟨_,hi⟩,Fin.ext rfl⟩
    · refine Or.inr ⟨⟨i.val-7,by have := i.isLt; omega⟩,Fin.ext ?_⟩
      change i.val=i.val-7+7
      omega
  refine ⟨F,?_,?_⟩
  · intro i j eq
    rcases elk i with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> rcases elk j with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · rw [vOld,vOld] at eq
      exact congrArg old (H.inj eq)
    · rw [vOld,vNew] at eq
      exact (off j i eq.symm).elim
    · rw [vOld,vNew] at eq
      exact (off i j eq).elim
    · rw [vNew,vNew] at eq
      exact congrArg new (fi eq)
  · intro i j
    rcases elk i with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> rcases elk j with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · rw [vOld,vOld,H.adj]
      simp [BRel,old,i.isLt,j.isLt]
    · rw [vOld,vNew,G.adj_comm,contact]
      have ge : ¬j.val+7 < 7 := by omega
      simp [BRel,old,new,i.isLt,ge,eq_comm]
    · rw [vOld,vNew,contact]
      have ge : ¬i.val+7 < 7 := by omega
      simp [BRel,old,new,j.isLt,ge,eq_comm]
    · rw [vNew,vNew,shape]
      have ge : ¬i.val+7 < 7 := by omega
      have ge' : ¬j.val+7 < 7 := by omega
      simp [BRel,new,ge,ge']

theorem no_exterior_bowtie_singleton_contacts (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (f : Fin 5 → V) (fi : Function.Injective f) (off : ∀ i, Outside H.c (f i))
    (shape : ∀ i j,G.Adj (f i) (f j) ↔ bowtie i j)
    (q0 : Fin 5 → Fin 7) (oldContact : ∀ i j,G.Adj (f i) (H.c j) ↔ j=q0 i) :
    False := by
  classical
  let r := q0 0
  let H' : Hole G 7 :=
    ⟨fun i => H.c (i+r), fun _ _ h => rot_inj r _ _ (H.inj h),
      fun i j => (H.adj _ _).trans (rot_cyc r i j)⟩
  let q (i : Fin 5) : Fin 7 := Classical.choose (rot_sur r (q0 i))
  have qadd (i : Fin 5) : q i+r=q0 i := Classical.choose_spec (rot_sur r (q0 i))
  have qz : q 0=0 := rot_inj r _ _ ((qadd 0).trans (by simp [r]))
  have ct (i : Fin 5) (j : Fin 7) : G.Adj (f i) (H'.c j) ↔ j=q i := by
    change G.Adj (f i) (H.c (j+r)) ↔ _
    rw [oldContact,←qadd i]
    exact ⟨rot_inj r _ _,fun e => congrArg (fun k : Fin 7 => k+r) e⟩
  have off' (i) : Outside H'.c (f i) := fun j => off i (j+r)
  have different {i j k : Fin 5} (ij : i≠j)
      (ik : G.Adj (f i) (f k)) (jk : G.Adj (f j) (f k)) : q i ≠ q j := by
    intro eq
    have ci := (ct i (q i)).mpr rfl
    have cj := (ct j (q i)).mpr eq
    exact off' k (q i) (h4 _ _ _ _ (fi.ne ij) ik jk ci cj)
  have noConsec {i j : Fin 5} (e : G.Adj (f i) (f j)) : ¬Cyclic (q i) (q j) := by
    intro cy
    have ci := (ct i (q i)).mpr rfl
    have cj := (ct j (q j)).mpr rfl
    have ad := (H'.adj _ _).mpr cy
    exact off' j (q i) (h4 _ _ _ _ (off' i (q j)) e cj.symm ci ad.symm)
  have tip (i : Fin 5) (nz : i≠0) : middle (q i) := by
    have E := (shape i 0).mpr (bow_from_root i nz)
    have pp := bow_partner i nz
    have ne := different (Ne.symm nz) ((shape 0 (partner i)).mpr pp.1) ((shape i (partner i)).mpr pp.2)
    have no := noConsec E.symm
    rw [qz] at ne no
    exact rootMiddle (q i) ne.symm no
  have tipNe (i j : Fin 5) (iz : i≠0) (jz : j≠0) (ij : i≠j) : q i≠q j :=
    different ij ((shape _ _).mpr (bow_from_root i iz)) ((shape _ _).mpr (bow_from_root j jz))
  have ok : norm (q 1) (q 2) (q 3) (q 4) := by
    exact ⟨tip 1 (by decide),tip 2 (by decide),tip 3 (by decide),tip 4 (by decide),
      tipNe 1 2 (by decide) (by decide) (by decide),tipNe 1 3 (by decide) (by decide) (by decide),
      tipNe 1 4 (by decide) (by decide) (by decide),tipNe 2 3 (by decide) (by decide) (by decide),
      tipNe 2 4 (by decide) (by decide) (by decide),tipNe 3 4 (by decide) (by decide) (by decide),
      noConsec ((shape 1 2).mpr (by decide)),noConsec ((shape 3 4).mpr (by decide))⟩
  obtain ⟨F,inj,adj⟩ := lift_model H' f fi off' shape q ct
  let p := witness (q 1) (q 2) (q 3) (q 4)
  have e : (![0,q 1,q 2,q 3,q 4] : Fin 5 → Fin 7)=q := by
    funext i
    fin_cases i
    · exact qz.symm
    · rfl
    · rfl
    · rfl
    · rfl
  have checked := certificate _ _ _ _ ok
  rw [e] at checked
  exact h9 ⟨F ∘ p,inj.comp (fun {_ _} => checked.1 _ _),
    fun i j hi => (adj _ _).trans (checked.2 _ _ hi)⟩

#print axioms no_exterior_bowtie_singleton_contacts

/-- Two exterior triangles sharing a vertex are the same triangle whenever
the exterior vertices have singleton contacts on the fixed induced heptagon. -/
theorem exterior_triangles_sharing_hub_same_tips [DecidableEq V]
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9 → V, InducedPath G p)
    (single : ∀ x, Outside H.c x → ∃ i, ∀ j,G.Adj x (H.c j) ↔ j=i)
    {u a b c d : V}
    (ou : Outside H.c u) (oa : Outside H.c a) (ob : Outside H.c b)
    (oc : Outside H.c c) (od : Outside H.c d)
    (ua : G.Adj u a) (ab : G.Adj a b) (bu : G.Adj b u)
    (uc : G.Adj u c) (cd : G.Adj c d) (du : G.Adj d u) :
    ({a,b}:Finset V)={c,d} := by
  classical
  by_cases eac : a=c
  · subst c
    have e : b=d := h4 u a b d ua.ne bu.symm ab du.symm cd
    rw [e]
  by_cases ead : a=d
  · subst d
    have e : b=c := h4 u a b c ua.ne bu.symm ab uc cd.symm
    rw [e,Finset.pair_comm]
  by_cases ebc : b=c
  · subst c
    have e : a=d := h4 u b a d bu.ne.symm ua ab.symm du.symm cd
    rw [e,Finset.pair_comm]
  by_cases ebd : b=d
  · subst d
    have e : a=c := h4 u b a c bu.ne.symm ua ab.symm uc cd.symm
    rw [e]
  have ac : ¬G.Adj a c := fun e => ebc (h4 a u b c ua.ne.symm ab bu.symm e uc)
  have ad : ¬G.Adj a d := fun e => ebd (h4 a u b d ua.ne.symm ab bu.symm e du.symm)
  have bc : ¬G.Adj b c := fun e => eac (h4 b u a c bu.ne ab.symm ua e uc)
  have bd : ¬G.Adj b d := fun e => ead (h4 b u a d bu.ne ab.symm ua e du.symm)
  let f : Fin 5 → V := ![u,a,b,c,d]
  have fi : Function.Injective f := List.nodup_ofFn.mp (by
    simpa [f,List.ofFn_succ] using (show [u,a,b,c,d].Nodup by
      simp [ua.ne,bu.ne.symm,uc.ne,du.ne.symm,ab.ne,eac,ead,ebc,ebd,cd.ne]))
  have exterior (i : Fin 5) : Outside H.c (f i) := by
    fin_cases i
    · exact ou
    · exact oa
    · exact ob
    · exact oc
    · exact od
  have shape (i j : Fin 5) : G.Adj (f i) (f j) ↔ bowtie i j := by
    have A : ¬ G.Adj c a := fun e => ac e.symm
    have B : ¬ G.Adj d a := fun e => ad e.symm
    have C : ¬ G.Adj c b := fun e => bc e.symm
    have D : ¬ G.Adj d b := fun e => bd e.symm
    fin_cases i <;> fin_cases j <;>
      simp [f,bowtie,ua,ua.symm,ab,ab.symm,bu,bu.symm,uc,uc.symm,cd,cd.symm,du,du.symm,
        ac,ad,bc,bd,A,B,C,D,G.loopless]
  choose q ct using fun i : Fin 5 => single (f i) (exterior i)
  exact (no_exterior_bowtie_singleton_contacts H h4 h9 f fi exterior shape q ct).elim

#print axioms exterior_triangles_sharing_hub_same_tips
end Graffiti133ExteriorBowtie
