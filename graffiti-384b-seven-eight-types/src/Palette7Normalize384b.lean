import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.VecNotation

namespace GraffitiSmallNorm7
open Finset SimpleGraph

def anchorTable : Fin 8 → Nat × Nat × Nat × Nat :=
  ![(0,4,4,3),(1,4,4,1),(1,4,4,2),(1,5,4,2),(1,4,4,3),(1,5,4,3),(1,5,5,3),(1,6,4,3)]

private noncomputable def join {X : Type*} (P : X → Prop) [DecidablePred P]
    {n m : Nat} (l : Fin n ≃ {x // P x}) (r : Fin m ≃ {x // ¬ P x}) : Fin (n+m) ≃ X :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr l r).trans (Equiv.sumCompl P))

private theorem joinL {X : Type*} (P : X → Prop) [DecidablePred P]
    {n m : Nat} (l : Fin n ≃ {x // P x}) (r : Fin m ≃ {x // ¬ P x}) (i : Fin n) :
    join P l r (Fin.castAdd m i) = (l i).val := by
  simp [join, Equiv.sumCompl]

private theorem joinR {X : Type*} (P : X → Prop) [DecidablePred P]
    {n m : Nat} (l : Fin n ≃ {x // P x}) (r : Fin m ≃ {x // ¬ P x}) (i : Fin m) :
    join P l r (Fin.natAdd n i) = (r i).val := by
  simp [join, Equiv.sumCompl]

private noncomputable def enum (X : Type*) [Fintype X] : Fin (Fintype.card X) ≃ X :=
  (Fintype.equivFin X).symm

private theorem card_sub_pred {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    Fintype.card {x // P x} = (Finset.univ.filter P).card := by
  let e : {x // P x} ≃ ↑(Finset.univ.filter P) :=
    Equiv.subtypeEquivRight (by intro x; simp)
  rw [Fintype.card_congr e, Fintype.card_coe]

private theorem card_join {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    Fintype.card {x // P x} + Fintype.card {x // ¬P x} = Fintype.card X := by
  rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl P)]

private theorem sorted_split_prefix {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P]
    (i : Fin (Fintype.card {x // P x} + Fintype.card {x // ¬ P x})) :
    P (join P (enum _) (enum _) i) ↔ i.val < Fintype.card {x // P x} := by
  obtain ⟨z,rfl⟩ := finSumFinEquiv.surjective i
  cases z with
  | inl k => rw [finSumFinEquiv_apply_left, joinL]; exact iff_of_true (Subtype.property _) k.isLt
  | inr k =>
    rw [finSumFinEquiv_apply_right, joinR]
    exact iff_of_false ((enum {x // ¬P x} k).property) (by simp)

private theorem allowed_quad :
    ∀ (t : Fin 2) (d e c : Fin 7), 4 ≤ e.val → e.val ≤ d.val → c.val ≤ 3 →
      c.val ≤ e.val-t.val → (d.val-t.val)+(e.val-t.val) ≤ 5+c.val →
      ∃ s, anchorTable s = (t.val,d.val,e.val,c.val) := by decide


private theorem sorted_two_preds {X : Type*} [Fintype X]
    (P Q : X → Prop) [DecidablePred P] [DecidablePred Q] :
    let a := Fintype.card {x // P x}
    let b := Fintype.card {x // Q x}
    let c := Fintype.card {x // P x ∧ Q x}
    ∃ e : Fin (Fintype.card X) ≃ X, ∀ i,
      (P (e i) ↔ i.val < a) ∧
      (Q (e i) ↔ i.val < c ∨ (a ≤ i.val ∧ i.val < a+b-c)) := by
  intro a b c
  let A := {x // P x}
  let B := {x // ¬P x}
  let QA : A → Prop := fun x => Q x
  let QB : B → Prop := fun x => Q x
  let ca := Fintype.card {x // QA x}
  let cb := Fintype.card {x // QB x}
  let la := Fintype.card {x // ¬ QA x}
  let lb := Fintype.card {x // ¬ QB x}
  have ha : ca+la = a := card_join QA
  have hb : cb+lb = Fintype.card B := card_join QB
  have htotal : a + Fintype.card B = Fintype.card X := card_join P
  have hca : ca = c := by
    apply Fintype.card_congr
    exact ⟨fun z => ⟨z.val.val, z.val.property, z.property⟩,
      fun z => ⟨⟨z.val,z.property.1⟩,z.property.2⟩,
      fun _ => rfl, fun _=>rfl⟩
  have hcb : b = ca+cb := by
    change Fintype.card {x // Q x} = _
    rw [← card_join (fun z : {x // Q x} => P z)]
    congr 1
    · apply Fintype.card_congr
      exact ⟨fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩,
        fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩,fun _ => rfl,fun _ => rfl⟩
    · apply Fintype.card_congr
      exact ⟨fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩,
        fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩,fun _ => rfl,fun _ => rfl⟩
  let eA := (finCongr ha.symm).trans (join QA (enum _) (enum _))
  let eB := (finCongr hb.symm).trans (join QB (enum _) (enum _))
  refine ⟨(finCongr htotal.symm).trans (join P eA eB),?_⟩
  intro i
  simp only [Equiv.trans_apply]
  generalize hh : finCongr htotal.symm i = j
  have val_eq : i.val = j.val := by rw [← hh]; rfl
  change (P (join P eA eB j) ↔ i.val < a) ∧
    (Q (join P eA eB j) ↔ i.val < c ∨ (a ≤ i.val ∧ i.val < a+b-c))
  obtain ⟨z,rfl⟩ := finSumFinEquiv.surjective j
  cases z with
  | inl k =>
    rw [finSumFinEquiv_apply_left, joinL] at *
    have vi : i.val = k.val := val_eq
    have hp : P (eA k).val := (eA k).property
    have hq : Q (eA k).val ↔ k.val < ca := sorted_split_prefix QA (finCongr ha.symm k)
    rw [vi,hq,iff_of_true hp k.isLt]
    have hh0 := k.isLt
    omega
  | inr k =>
    rw [finSumFinEquiv_apply_right, joinR] at *
    have vi : i.val = a + k.val := val_eq
    have hp : ¬P (eB k).val := (eB k).property
    have hq : Q (eB k).val ↔ k.val < cb := sorted_split_prefix QB (finCongr hb.symm k)
    rw [vi,hq,iff_of_false hp (by omega : ¬ a+k.val<a)]
    omega


private theorem card_cut {X : Type*} [Fintype X] (P Q : X → Prop)
    [DecidablePred P] [DecidablePred Q] (S : Finset X)
    (h : ∀ x, x∈S ↔ P x ∧ Q x) :
    Fintype.card {z : {x // P x} // Q z.val} = S.card := by
  let e : {z : {x // P x} // Q z.val} ≃ ↑S :=
    ⟨fun z => ⟨z.val.val, (h _).mpr ⟨z.val.property,z.property⟩⟩,
     fun z => ⟨⟨z.val,((h _).mp z.property).1⟩,((h _).mp z.property).2⟩,
     fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e,Fintype.card_coe]

private theorem normalize_ordered (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (x y : Fin 7) (xy : x ≠ y) (hy : 4 ≤ G.degree y) (ord : G.degree y ≤ G.degree x)
    (hc : (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 3) :
    ∃ (s : Fin 8) (p : Fin 7 ≃ Fin 7),
      p 0 = x ∧ p 1 = y ∧
      (G.Adj (p 0) (p 1) ↔ (anchorTable s).1 = 1) ∧
      ∀ j : Fin 7, 2 ≤ j.val →
        let t := anchorTable s
        let a := t.2.1 - t.1
        let b := t.2.2.1 - t.1
        let c := t.2.2.2
        let r := j.val - 2
        (G.Adj (p 0) (p j) ↔ r < a) ∧
        (G.Adj (p 1) (p j) ↔ r < c ∨ (a ≤ r ∧ r < a+b-c)) := by
  classical
  let A := (G.neighborFinset x).erase y
  let B := (G.neighborFinset y).erase x
  let C := G.neighborFinset x ∩ G.neighborFinset y
  let W : Finset (Fin 7) := (Finset.univ.erase y).erase x
  have wc : W.card = 5 := by simp [W,Finset.card_erase_of_mem,xy]
  let anchor (v : Fin 7) := v=x ∨ v=y
  let Z := {v // ¬ anchor v}
  let t : Fin 2 := if G.Adj x y then 1 else 0
  have tc : t.val = if G.Adj x y then 1 else 0 := by by_cases e : G.Adj x y <;> simp [t,e]
  have ac : A.card = G.degree x - t.val := by
    rw [tc]
    by_cases ed : G.Adj x y
    · simp [A,ed,Finset.card_erase_of_mem ((G.mem_neighborFinset x y).mpr ed),G.card_neighborFinset_eq_degree]
    · have notM : y ∉ G.neighborFinset x := by simpa using ed
      simp [A,ed,Finset.erase_eq_of_not_mem notM,G.card_neighborFinset_eq_degree]
  have bc : B.card = G.degree y - t.val := by
    rw [tc]
    by_cases ed : G.Adj x y
    · simp [B,ed,Finset.card_erase_of_mem ((G.mem_neighborFinset y x).mpr ed.symm),G.card_neighborFinset_eq_degree]
    · have notM : x ∉ G.neighborFinset y := by simpa [G.adj_comm] using ed
      simp [B,ed,Finset.erase_eq_of_not_mem notM,G.card_neighborFinset_eq_degree]
  have wi (v : Fin 7) : v∈W ↔ ¬ anchor v := by simp [W,anchor]
  have ai (v : Fin 7) : v∈A ↔ ¬ anchor v ∧ G.Adj x v := by
    simp only [A,Finset.mem_erase,G.mem_neighborFinset,anchor,not_or]
    constructor
    · rintro ⟨ne,adj⟩
      exact ⟨⟨adj.ne.symm,ne⟩,adj⟩
    · rintro ⟨⟨_,ne⟩,adj⟩
      exact ⟨ne,adj⟩
  have bi (v : Fin 7) : v∈B ↔ ¬ anchor v ∧ G.Adj y v := by
    simp only [B,Finset.mem_erase,G.mem_neighborFinset,anchor,not_or]
    constructor
    · rintro ⟨ne,adj⟩
      exact ⟨⟨ne,adj.ne.symm⟩,adj⟩
    · rintro ⟨⟨ne,_⟩,adj⟩
      exact ⟨ne,adj⟩
  have ci (v : Fin 7) : v∈C ↔ ¬ anchor v ∧ (G.Adj x v ∧ G.Adj y v) := by
    simp only [C,Finset.mem_inter,G.mem_neighborFinset,anchor,not_or]
    constructor
    · rintro ⟨adj,adj'⟩
      exact ⟨⟨adj.ne.symm,adj'.ne.symm⟩,adj,adj'⟩
    · exact And.right
  have inter : A ∩ B = C := by ext v; rw [Finset.mem_inter,ai,bi,ci]; tauto
  have sub : A ∪ B ⊆ W := by
    intro v hv
    rw [wi]
    rcases Finset.mem_union.mp hv with ha | hb
    · exact (ai v |>.mp ha).1
    · exact (bi v |>.mp hb).1
  have unionc := Finset.card_le_card sub
  have commonB : C.card ≤ B.card := Finset.card_le_card (inter ▸ Finset.inter_subset_right)
  have sumAB := Finset.card_union_add_card_inter A B
  rw [inter,ac,bc] at sumAB
  have hdx : G.degree x < 7 := by simpa using G.degree_lt_card_verts x
  have hdy : G.degree y < 7 := by simpa using G.degree_lt_card_verts y
  change C.card ≤ 3 at hc
  obtain ⟨s, hs⟩ := allowed_quad t ⟨G.degree x,hdx⟩ ⟨G.degree y,hdy⟩ ⟨C.card,by omega⟩
    hy ord hc (by simpa only [bc] using commonB) (by rw [wc] at unionc; simp only; omega)
  have dz : Fintype.card Z = 5 := by
    rw [card_sub_pred]
    have e : (Finset.univ.filter fun v => ¬anchor v) = W := by ext v; simp [wi]
    rw [e,wc]
  let LX : Z → Prop := fun z => G.Adj x z.val
  let LY : Z → Prop := fun z => G.Adj y z.val
  obtain ⟨zEq, zSpec⟩ := sorted_two_preds LX LY
  have za : Fintype.card {z // LX z} = A.card := card_cut _ _ _ ai
  have zb : Fintype.card {z // LY z} = B.card := card_cut _ _ _ bi
  have zc : Fintype.card {z // LX z ∧ LY z} = C.card := card_cut _ _ _ ci
  let v : Fin 2 → {u // anchor u} := fun i =>
    if i=0 then ⟨x,Or.inl rfl⟩ else ⟨y,Or.inr rfl⟩
  have vv : Function.Bijective v := by
    refine ⟨?_,?_⟩
    · intro i j e
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso; exact xy (congrArg Subtype.val e)
      · exfalso; exact xy (congrArg Subtype.val e).symm
      · rfl
    · intro u
      rcases u.property with hu|hu
      · exact ⟨0, Subtype.ext hu.symm⟩
      · exact ⟨1, Subtype.ext hu.symm⟩
  let left := Equiv.ofBijective v vv
  let right := (finCongr dz.symm).trans zEq
  let p : Fin 7 ≃ Fin 7 := join anchor left right
  have px : p 0 = x := by
    change join anchor left right (Fin.castAdd 5 (0 : Fin 2)) = x
    rw [joinL]
    rfl
  have py : p 1 = y := by
    change join anchor left right (Fin.castAdd 5 (1 : Fin 2)) = y
    rw [joinL]
    rfl
  refine ⟨s,p,px,py,?_,?_⟩
  · rw [px,py,hs]
    change G.Adj x y ↔ t.val = 1
    rw [tc]; by_cases e : G.Adj x y <;> simp [e]
  · intro j hj
    let k : Fin 5 := ⟨j.val-2,by have b := j.isLt; omega⟩
    have jEq : Fin.natAdd 2 k = j := by apply Fin.ext; change 2+(j.val-2)=j.val; omega
    have jp : p j = (right k).val := by rw [← jEq]; exact joinR anchor left right k
    have h := zSpec (finCongr dz.symm k)
    rw [za,zb,zc,ac,bc] at h
    simpa only [px,py,hs,jp, LX, LY] using h

theorem normalize_two_anchors (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (x y : Fin 7) (xy : x ≠ y) (hx : 4 ≤ G.degree x) (hy : 4 ≤ G.degree y)
    (hc : (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 3) :
    ∃ (s : Fin 8) (p : Fin 7 ≃ Fin 7),
      ((p 0 = x ∧ p 1 = y) ∨ (p 0 = y ∧ p 1 = x)) ∧
      (G.Adj (p 0) (p 1) ↔ (anchorTable s).1 = 1) ∧
      ∀ j : Fin 7, 2 ≤ j.val →
        let t := anchorTable s
        let a := t.2.1 - t.1
        let b := t.2.2.1 - t.1
        let c := t.2.2.2
        let r := j.val - 2
        (G.Adj (p 0) (p j) ↔ r < a) ∧
        (G.Adj (p 1) (p j) ↔ r < c ∨ (a ≤ r ∧ r < a+b-c)) := by
  by_cases ord : G.degree y ≤ G.degree x
  · obtain ⟨s,p,hx,hy,rest⟩ := normalize_ordered G x y xy hy ord hc
    exact ⟨s,p,Or.inl ⟨hx,hy⟩,rest⟩
  · have ord' : G.degree x ≤ G.degree y := by omega
    obtain ⟨s,p,hy,hx,rest⟩ := normalize_ordered G y x xy.symm hx ord' (by simpa [Finset.inter_comm] using hc)
    exact ⟨s,p,Or.inr ⟨hy,hx⟩,rest⟩

end GraffitiSmallNorm7

#print axioms GraffitiSmallNorm7.normalize_two_anchors
