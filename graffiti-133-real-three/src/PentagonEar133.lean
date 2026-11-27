import PentagonStructure133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

private def TypeContact (t : Fin 10) (i : Fin 5) : Prop :=
  if h : t.val < 5 then i = (⟨t.val,h⟩ : Fin 5)
  else i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) ∨
    i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) + 1
private noncomputable instance (t : Fin 10) : DecidablePred (TypeContact t) := by
  intro i
  unfold TypeContact
  split <;> infer_instance

private def RootContact (t : Fin 10) (d : Bool) (q : Fin 8) (i : Fin 5) : Prop :=
  if q = 5 then i = 0 else if q = 6 then i = 2 ∨ (d = true ∧ i = 3)
  else TypeContact t i
private noncomputable instance (t : Fin 10) (d : Bool) (q : Fin 8) :
    DecidablePred (RootContact t d q) := by
  intro i
  unfold RootContact
  split
  · infer_instance
  · split <;> infer_instance

private def earRel (t : Fin 10) (d a b : Bool) (x y : Fin 8) : Prop :=
  if hx : x.val < 5 then
    if hy : y.val < 5 then pent ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else RootContact t d y ⟨x.val,hx⟩
  else if hy : y.val < 5 then RootContact t d x ⟨y.val,hy⟩
  else ((x = 5 ∧ y = 6) ∨ (x = 6 ∧ y = 5)) ∨
    (a = true ∧ ((x = 5 ∧ y = 7) ∨ (x = 7 ∧ y = 5))) ∨
    (b = true ∧ ((x = 6 ∧ y = 7) ∨ (x = 7 ∧ y = 6)))
private noncomputable instance (t : Fin 10) (d a b : Bool) : DecidableRel (earRel t d a b) := by
  intro i j
  unfold earRel
  split <;> split <;> infer_instance

private inductive EarCert
| near
| via (i : Fin 8)
| four (i j a b : Fin 8)
| path (p : Fin 6 → Fin 8)

private def certTrue (R : Fin 8 → Fin 8 → Prop) : EarCert → Prop
| .near => R 0 7
| .via i => R 0 i ∧ R i 7
| .four i j a b => i ≠ j ∧ a ≠ b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i = p j → i = j) ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)

private noncomputable instance (R : Fin 8 → Fin 8 → Prop) [DecidableRel R] :
    DecidablePred (certTrue R) := by
  intro e
  cases e <;> unfold certTrue <;> infer_instance

private def earTable (t : Fin 10) (d a b : Bool) : EarCert :=
  match t.val, d, a, b with
  | 0, false, false, false => .near
  | 0, false, false, true => .near
  | 0, false, true, false => .near
  | 0, false, true, true => .near
  | 0, true, false, false => .near
  | 0, true, false, true => .near
  | 0, true, true, false => .near
  | 0, true, true, true => .near
  | 1, false, false, false => .via 1
  | 1, false, false, true => .via 1
  | 1, false, true, false => .via 1
  | 1, false, true, true => .via 1
  | 1, true, false, false => .via 1
  | 1, true, false, true => .via 1
  | 1, true, true, false => .via 1
  | 1, true, true, true => .via 1
  | 2, false, false, false => .path ![4, 0, 5, 6, 2, 7]
  | 2, false, false, true => .path ![3, 4, 0, 5, 6, 7]
  | 2, false, true, false => .via 5
  | 2, false, true, true => .via 5
  | 2, true, false, false => .path ![4, 0, 5, 6, 2, 7]
  | 2, true, false, true => .four 2 6 3 7
  | 2, true, true, false => .via 5
  | 2, true, true, true => .via 5
  | 3, false, false, false => .path ![0, 5, 6, 2, 3, 7]
  | 3, false, false, true => .four 2 7 3 6
  | 3, false, true, false => .via 5
  | 3, false, true, true => .via 5
  | 3, true, false, false => .path ![1, 0, 5, 6, 3, 7]
  | 3, true, false, true => .four 2 7 3 6
  | 3, true, true, false => .via 5
  | 3, true, true, true => .via 5
  | 4, false, false, false => .via 4
  | 4, false, false, true => .via 4
  | 4, false, true, false => .via 4
  | 4, false, true, true => .via 4
  | 4, true, false, false => .via 4
  | 4, true, false, true => .via 4
  | 4, true, true, false => .via 4
  | 4, true, true, true => .via 4
  | 5, false, false, false => .near
  | 5, false, false, true => .near
  | 5, false, true, false => .near
  | 5, false, true, true => .near
  | 5, true, false, false => .near
  | 5, true, false, true => .near
  | 5, true, true, false => .near
  | 5, true, true, true => .near
  | 6, false, false, false => .via 1
  | 6, false, false, true => .via 1
  | 6, false, true, false => .via 1
  | 6, false, true, true => .via 1
  | 6, true, false, false => .via 1
  | 6, true, false, true => .via 1
  | 6, true, true, false => .via 1
  | 6, true, true, true => .via 1
  | 7, false, false, false => .path ![4, 0, 5, 6, 2, 7]
  | 7, false, false, true => .four 2 7 3 6
  | 7, false, true, false => .via 5
  | 7, false, true, true => .via 5
  | 7, true, false, false => .four 2 3 6 7
  | 7, true, false, true => .four 2 3 6 7
  | 7, true, true, false => .via 5
  | 7, true, true, true => .via 5
  | 8, false, false, false => .via 4
  | 8, false, false, true => .via 4
  | 8, false, true, false => .via 4
  | 8, false, true, true => .via 4
  | 8, true, false, false => .via 4
  | 8, true, false, true => .via 4
  | 8, true, true, false => .via 4
  | 8, true, true, true => .via 4
  | 9, false, false, false => .near
  | 9, false, false, true => .near
  | 9, false, true, false => .near
  | 9, false, true, true => .near
  | 9, true, false, false => .near
  | 9, true, false, true => .near
  | 9, true, true, false => .near
  | 9, true, true, true => .near
  | _, _, _, _ => .near

private theorem checkEar : ∀ t d a b, certTrue (earRel t d a b) (earTable t d a b) := by
  decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

private lemma type_of_outside {z : V} (hz : Outside F.c z) :
    ∃ t, ∀ i, G.Adj z (F.c i) ↔ TypeContact t i := by
  rcases F.classify_contact z hz with ⟨i,hi⟩ | ⟨i,hi⟩
  · refine ⟨⟨i.val,by have := i.isLt; omega⟩,fun j => (hi.2 j).trans ?_⟩
    have he : i.val < 5 := i.isLt
    simp [TypeContact,he]
  · refine ⟨⟨i.val+5,by have := i.isLt; omega⟩,fun j => (hi.2 j).trans ?_⟩
    have he : ¬i.val+5 < 5 := by omega
    have he' : (⟨i.val+5-5,by have := i.isLt; omega⟩ : Fin 5) = i := Fin.ext (by simp)
    simp [TypeContact,he,he']


private lemma outside_cases : ∀ i : Fin 8, ¬ i.val < 5 → i = 5 ∨ i = 6 ∨ i = 7 := by decide

private lemma d2_of_walk {a b c : V} (h₁ : G.Adj a b) (h₂ : G.Adj b c) :
    G.dist a c ≤ 2 := by simpa using G.dist_le (Walk.cons h₁ (Walk.cons h₂ .nil))

private lemma d1_of_adj {a b : V} (h : G.Adj a b) : G.dist a b ≤ 2 := by
  rw [dist_eq_one_iff_adj.mpr h]
  decide

private lemma ground_near : ∀ i : Fin 5,
    i = 0 ∨ pent 0 i ∨ (∃ j, pent 0 j ∧ pent j i) := by decide

private theorem dist_ear_new {x y z : V}
    (hx : One G F.c x 0) (hy : One G F.c y 2 ∨ Two G F.c y 2) (exy : G.Adj x y)
    (hz : Outside F.c z) (zx : z ≠ x) (zy : z ≠ y) :
    G.dist (F.c 0) z ≤ 2 := by
  classical
  obtain ⟨t,ht⟩ := F.type_of_outside hz
  obtain ⟨d,hyO,ry⟩ : ∃ d : Bool, Outside F.c y ∧
      ∀ i : Fin 5, G.Adj y (F.c i) ↔ (i = 2 ∨ (d = true ∧ i = 3)) := by
    rcases hy with h | h
    · exact ⟨false,h.1,fun i => by simpa using h.2 i⟩
    · exact ⟨true,h.1,fun i => by simpa using h.2 i⟩
  let a : Bool := decide (G.Adj x z)
  let b : Bool := decide (G.Adj y z)
  have aTrue : a = true ↔ G.Adj x z := by simp [a]
  have bTrue : b = true ↔ G.Adj y z := by simp [b]
  let g (i : Fin 8) : V :=
    if hi : i.val < 5 then F.c ⟨i.val,hi⟩
    else if i = 5 then x else if i = 6 then y else z
  have gx : g 5 = x := rfl
  have gy : g 6 = y := rfl
  have gz : g 7 = z := rfl
  have g0 : g 0 = F.c 0 := rfl
  have inj : Function.Injective g := by
    intro i j eq
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · have e : F.c ⟨i.val,hi⟩ = F.c ⟨j.val,hj⟩ := by
        simpa only [g,dif_pos hi,dif_pos hj] using eq
      exact Fin.ext (congrArg (fun i : Fin 5 => i.val) (F.inj e))
    · rcases outside_cases j hj with rfl | rfl | rfl
      · exact (hx.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gx] using eq.symm)).elim
      · exact (hyO ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gy] using eq.symm)).elim
      · exact (hz ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gz] using eq.symm)).elim
    · rcases outside_cases i hi with rfl | rfl | rfl
      · exact (hx.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gx] using eq)).elim
      · exact (hyO ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gy] using eq)).elim
      · exact (hz ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gz] using eq)).elim
    · rcases outside_cases i hi with rfl | rfl | rfl <;>
        rcases outside_cases j hj with rfl | rfl | rfl <;>
          first | rfl | exact (exy.ne eq).elim | exact (exy.ne eq.symm).elim |
            exact (zx eq).elim | exact (zx eq.symm).elim |
            exact (zy eq).elim | exact (zy eq.symm).elim
  have rightContact (i : Fin 8) (hi : ¬i.val < 5) (j : Fin 5) :
      G.Adj (g i) (F.c j) ↔ RootContact t d i j := by
    rcases outside_cases i hi with rfl | rfl | rfl
    · rw [gx]
      exact (hx.2 j).trans (by simp [RootContact])
    · rw [gy]
      exact (ry j).trans (by simp [RootContact])
    · rw [gz]
      exact (ht j).trans (by simp [RootContact])
  have lift (i j : Fin 8) : G.Adj (g i) (g j) ↔ earRel t d a b i j := by
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · simpa only [g,earRel,dif_pos hi,dif_pos hj] using F.adj ⟨_,hi⟩ ⟨_,hj⟩
    · rw [earRel,dif_pos hi,dif_neg hj,show g i = F.c ⟨i.val,hi⟩ from dif_pos hi,G.adj_comm,
        rightContact j hj]
    · rw [earRel,dif_neg hi,dif_pos hj,show g j = F.c ⟨j.val,hj⟩ from dif_pos hj,
        rightContact i hi]
    · rcases outside_cases i hi with rfl | rfl | rfl <;>
        rcases outside_cases j hj with rfl | rfl | rfl
      all_goals simp [earRel,hi,hj,gx,gy,gz,exy,exy.symm,G.loopless,aTrue,bTrue]
      all_goals exact G.adj_comm _ _
  have cert := checkEar t d a b
  cases he : earTable t d a b with
  | near =>
    have er : earRel t d a b 0 7 := by simpa only [he,certTrue] using cert
    have eg := (lift _ _).mpr er
    rw [g0,gz] at eg
    exact d1_of_adj eg
  | via i =>
    have er : earRel t d a b 0 i ∧ earRel t d a b i 7 := by
      simpa only [he,certTrue] using cert
    have eg := (lift _ _).mpr er.1
    have eg' := (lift _ _).mpr er.2
    rw [g0] at eg
    rw [gz] at eg'
    exact d2_of_walk eg eg'
  | four i j p q =>
    have er : i ≠ j ∧ p ≠ q ∧ earRel t d a b i p ∧ earRel t d a b j p ∧
        earRel t d a b i q ∧ earRel t d a b j q := by
      simpa only [he,certTrue] using cert
    obtain ⟨nij,npq,ip,jp,iq,jq⟩ := er
    have contra := F.h4 _ _ _ _ (fun e => nij (inj e)) ((lift _ _).mpr ip)
      ((lift _ _).mpr jp) ((lift _ _).mpr iq) ((lift _ _).mpr jq)
    exact (npq (inj contra)).elim
  | path p =>
    have er : (∀ i j, p i = p j → i = j) ∧
        ∀ i j : Fin 6, i < j → (earRel t d a b (p i) (p j) ↔ i.val+1=j.val) := by
      simpa only [he,certTrue] using cert
    exact (F.noP6 ⟨g ∘ p,inj.comp er.1,fun i j h => (lift _ _).trans (er.2 i j h)⟩).elim

private lemma radius_ecc (u : V) : radius G ≤ Finset.univ.sup (G.dist u) := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist u) ∈
      Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  cases hmin : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d => simpa [hmin] using hl

/-- An outside edge between the indicated distinct contact types forces
radius at most two in a P6-free pentagon frame. -/
theorem anchored_ear_radius {x y : V} (hx : One G F.c x 0)
    (hy : One G F.c y 2 ∨ Two G F.c y 2) (e : G.Adj x y) :
    radius G ≤ 2 := by
  apply (radius_ecc (G:=G) (F.c 0)).trans
  apply Finset.sup_le_iff.mpr
  intro z _
  by_cases out : Outside F.c z
  · by_cases zx : z = x
    · exact zx.symm ▸ d1_of_adj ((hx.2 0).mpr rfl).symm
    · by_cases zy : z = y
      · exact zy.symm ▸ d2_of_walk ((hx.2 0).mpr rfl).symm e
      · exact F.dist_ear_new hx hy e out zx zy
  · obtain ⟨i,hi⟩ : ∃ i, z = F.c i := by
      apply Classical.byContradiction
      intro no
      exact out (fun j e => no ⟨j,e⟩)
    rw [hi]
    rcases ground_near i with eq | adj | ⟨j,e1,e2⟩
    · simp [eq,SimpleGraph.dist_self]
    · exact d1_of_adj ((F.adj _ _).mpr adj)
    · exact d2_of_walk ((F.adj _ _).mpr e1) ((F.adj _ _).mpr e2)

#print axioms anchored_ear_radius

end PentagonFrame
end Graffiti133Pentagon
