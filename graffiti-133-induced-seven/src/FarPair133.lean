import FarPentagon133

namespace Graffiti133FarPentagon
namespace Frame
open SimpleGraph Graffiti133 Graffiti133Pentagon Graffiti133NoFive
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

private def TypeContact (t : Fin 10) (i : Fin 5) : Prop :=
  if h : t.val < 5 then i = (⟨t.val,h⟩ : Fin 5)
  else i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) ∨
    i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) + 1
private noncomputable instance (t : Fin 10) : DecidablePred (TypeContact t) := by
  intro i
  unfold TypeContact
  split <;> infer_instance

private def RootContact (t u : Fin 10) (q : Fin 8) (i : Fin 5) : Prop :=
  if q = 5 then TypeContact t i else if q = 6 then TypeContact u i else False
private noncomputable instance (t u : Fin 10) (q : Fin 8) :
    DecidablePred (RootContact t u q) := by
  intro i
  unfold RootContact
  split
  · infer_instance
  · split <;> infer_instance

private def farRel (t u : Fin 10) (x y : Fin 8) : Prop :=
  if hx : x.val < 5 then
    if hy : y.val < 5 then pent ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else RootContact t u y ⟨x.val,hx⟩
  else if hy : y.val < 5 then RootContact t u x ⟨y.val,hy⟩
  else (x = 7 ∧ (y = 5 ∨ y = 6)) ∨ (y = 7 ∧ (x = 5 ∨ x = 6))
private noncomputable instance (t u : Fin 10) : DecidableRel (farRel t u) := by
  intro i j
  unfold farRel
  split <;> split <;> infer_instance

private inductive Cert
| four (i j a b : Fin 8)
| path (p : Fin 7 → Fin 8)
| hole6 (c : Fin 6 → Fin 8)
| hole7 (c : Fin 7 → Fin 8)

private def certTrue (R : Fin 8 → Fin 8 → Prop) : Cert → Prop
| .four i j a b => i ≠ j ∧ a ≠ b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i = p j → i = j) ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)
| .hole6 c => (∀ i j, c i = c j → i = j) ∧ ∀ i j, R (c i) (c j) ↔ Cyclic i j
| .hole7 c => (∀ i j, c i = c j → i = j) ∧ ∀ i j, R (c i) (c j) ↔ Cyclic i j

private noncomputable instance (R : Fin 8 → Fin 8 → Prop) [DecidableRel R] :
    DecidablePred (certTrue R) := by
  intro e
  cases e <;> unfold certTrue <;> infer_instance

private def farTable (t u : Fin 10) : Cert :=
  match t.val,u.val with
  | 0, 0 => .four 0 7 5 6
  | 0, 1 => .path ![2,3,4,0,5,7,6]
  | 0, 2 => .hole6 ![0,1,2,6,7,5]
  | 0, 3 => .hole6 ![0,4,3,6,7,5]
  | 0, 4 => .path ![1,2,3,4,6,7,5]
  | 0, 5 => .four 0 7 5 6
  | 0, 6 => .hole7 ![0,4,3,2,6,7,5]
  | 0, 7 => .hole6 ![0,1,2,6,7,5]
  | 0, 8 => .hole7 ![0,1,2,3,6,7,5]
  | 0, 9 => .four 0 7 5 6
  | 1, 0 => .path ![2,3,4,0,6,7,5]
  | 1, 1 => .four 1 7 5 6
  | 1, 2 => .path ![0,4,3,2,6,7,5]
  | 1, 3 => .hole6 ![1,2,3,6,7,5]
  | 1, 4 => .hole6 ![0,1,5,7,6,4]
  | 1, 5 => .four 1 7 5 6
  | 1, 6 => .four 1 7 5 6
  | 1, 7 => .hole7 ![0,1,5,7,6,3,4]
  | 1, 8 => .hole6 ![0,1,5,7,6,4]
  | 1, 9 => .hole7 ![1,2,3,4,6,7,5]
  | 2, 0 => .hole6 ![0,1,2,5,7,6]
  | 2, 1 => .path ![0,4,3,2,5,7,6]
  | 2, 2 => .four 2 7 5 6
  | 2, 3 => .path ![1,0,4,3,6,7,5]
  | 2, 4 => .hole6 ![2,3,4,6,7,5]
  | 2, 5 => .hole7 ![0,4,3,2,5,7,6]
  | 2, 6 => .four 2 7 5 6
  | 2, 7 => .four 2 7 5 6
  | 2, 8 => .hole7 ![0,1,2,5,7,6,4]
  | 2, 9 => .hole6 ![0,1,2,5,7,6]
  | 3, 0 => .hole6 ![0,4,3,5,7,6]
  | 3, 1 => .hole6 ![1,2,3,5,7,6]
  | 3, 2 => .path ![1,0,4,3,5,7,6]
  | 3, 3 => .four 3 7 5 6
  | 3, 4 => .path ![0,1,2,3,5,7,6]
  | 3, 5 => .hole6 ![0,4,3,5,7,6]
  | 3, 6 => .hole7 ![0,1,6,7,5,3,4]
  | 3, 7 => .four 3 7 5 6
  | 3, 8 => .four 3 7 5 6
  | 3, 9 => .hole7 ![0,1,2,3,5,7,6]
  | 4, 0 => .path ![1,2,3,4,5,7,6]
  | 4, 1 => .hole6 ![0,1,6,7,5,4]
  | 4, 2 => .hole6 ![2,3,4,5,7,6]
  | 4, 3 => .path ![0,1,2,3,6,7,5]
  | 4, 4 => .four 4 7 5 6
  | 4, 5 => .hole7 ![1,2,3,4,5,7,6]
  | 4, 6 => .hole6 ![0,1,6,7,5,4]
  | 4, 7 => .hole7 ![0,1,2,6,7,5,4]
  | 4, 8 => .four 4 7 5 6
  | 4, 9 => .four 4 7 5 6
  | 5, 0 => .four 0 7 5 6
  | 5, 1 => .four 1 7 5 6
  | 5, 2 => .hole7 ![0,4,3,2,6,7,5]
  | 5, 3 => .hole6 ![0,4,3,6,7,5]
  | 5, 4 => .hole7 ![1,2,3,4,6,7,5]
  | 5, 5 => .four 0 1 5 6
  | 5, 6 => .four 1 7 5 6
  | 5, 7 => .hole6 ![0,4,3,6,7,5]
  | 5, 8 => .hole6 ![1,2,3,6,7,5]
  | 5, 9 => .four 0 7 5 6
  | 6, 0 => .hole7 ![0,4,3,2,5,7,6]
  | 6, 1 => .four 1 7 5 6
  | 6, 2 => .four 2 7 5 6
  | 6, 3 => .hole7 ![0,1,5,7,6,3,4]
  | 6, 4 => .hole6 ![0,1,5,7,6,4]
  | 6, 5 => .four 1 7 5 6
  | 6, 6 => .four 1 2 5 6
  | 6, 7 => .four 2 7 5 6
  | 6, 8 => .hole6 ![0,1,5,7,6,4]
  | 6, 9 => .hole6 ![2,3,4,6,7,5]
  | 7, 0 => .hole6 ![0,1,2,5,7,6]
  | 7, 1 => .hole7 ![0,1,6,7,5,3,4]
  | 7, 2 => .four 2 7 5 6
  | 7, 3 => .four 3 7 5 6
  | 7, 4 => .hole7 ![0,1,2,5,7,6,4]
  | 7, 5 => .hole6 ![0,4,3,5,7,6]
  | 7, 6 => .four 2 7 5 6
  | 7, 7 => .four 2 3 5 6
  | 7, 8 => .four 3 7 5 6
  | 7, 9 => .hole6 ![0,1,2,5,7,6]
  | 8, 0 => .hole7 ![0,1,2,3,5,7,6]
  | 8, 1 => .hole6 ![0,1,6,7,5,4]
  | 8, 2 => .hole7 ![0,1,2,6,7,5,4]
  | 8, 3 => .four 3 7 5 6
  | 8, 4 => .four 4 7 5 6
  | 8, 5 => .hole6 ![1,2,3,5,7,6]
  | 8, 6 => .hole6 ![0,1,6,7,5,4]
  | 8, 7 => .four 3 7 5 6
  | 8, 8 => .four 3 4 5 6
  | 8, 9 => .four 4 7 5 6
  | 9, 0 => .four 0 7 5 6
  | 9, 1 => .hole7 ![1,2,3,4,5,7,6]
  | 9, 2 => .hole6 ![0,1,2,6,7,5]
  | 9, 3 => .hole7 ![0,1,2,3,6,7,5]
  | 9, 4 => .four 4 7 5 6
  | 9, 5 => .four 0 7 5 6
  | 9, 6 => .hole6 ![2,3,4,5,7,6]
  | 9, 7 => .hole6 ![0,1,2,6,7,5]
  | 9, 8 => .four 4 7 5 6
  | 9, 9 => .four 0 4 5 6
  | _, _ => .four 0 0 0 0

private theorem checkFar : ∀ t u, certTrue (farRel t u) (farTable t u) := by decide
private lemma outside_cases : ∀ i : Fin 8, ¬ i.val < 5 → i = 5 ∨ i = 6 ∨ i = 7 := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

private lemma type_of_near {z : V} (hz : Near F z) :
    ∃ t, ∀ i, G.Adj z (F.c i) ↔ TypeContact t i := by
  rcases F.classify hz with ⟨i,hi⟩ | ⟨i,hi⟩
  · refine ⟨⟨i.val,by have := i.isLt; omega⟩,fun j => (hi.2 j).trans ?_⟩
    have he : i.val < 5 := i.isLt
    simp [TypeContact,he]
  · refine ⟨⟨i.val+5,by have := i.isLt; omega⟩,fun j => (hi.2 j).trans ?_⟩
    have he : ¬i.val+5 < 5 := by omega
    have he' : (⟨i.val+5-5,by have := i.isLt; omega⟩ : Fin 5) = i := Fin.ext (by simp)
    simp [TypeContact,he,he']

/-- For a far vertex with two nonadjacent distinct neighbors on the
pentagon frontier, a square, P7, or induced C6/C7 is forced. -/
theorem far_pair_forces_hole {x y z : V} (hx : Near F x) (hy : Near F y) (hz : Far F z)
    (xy : x ≠ y) (nxy : ¬G.Adj x y) (exz : G.Adj x z) (eyz : G.Adj y z)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) : Nonempty (Hole G 6) ∨ Nonempty (Hole G 7) := by
  classical
  obtain ⟨t,ht⟩ := F.type_of_near hx
  obtain ⟨u,hu⟩ := F.type_of_near hy
  let g (i : Fin 8) : V :=
    if hi : i.val < 5 then F.c ⟨i.val,hi⟩
    else if i = 5 then x else if i = 6 then y else z
  have gx : g 5 = x := rfl
  have gy : g 6 = y := rfl
  have gz : g 7 = z := rfl
  have inj : Function.Injective g := by
    intro i j eq
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · have e : F.c ⟨i.val,hi⟩ = F.c ⟨j.val,hj⟩ := by
        simpa only [g,dif_pos hi,dif_pos hj] using eq
      exact Fin.ext (congrArg (fun i : Fin 5 => i.val) (F.inj e))
    · rcases outside_cases j hj with rfl | rfl | rfl
      · exact (hx.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gx] using eq.symm)).elim
      · exact (hy.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gy] using eq.symm)).elim
      · exact (hz.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gz] using eq.symm)).elim
    · rcases outside_cases i hi with rfl | rfl | rfl
      · exact (hx.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gx] using eq)).elim
      · exact (hy.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gy] using eq)).elim
      · exact (hz.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gz] using eq)).elim
    · rcases outside_cases i hi with rfl | rfl | rfl <;>
        rcases outside_cases j hj with rfl | rfl | rfl <;>
          first | rfl | exact (xy eq).elim | exact (xy eq.symm).elim |
            exact (exz.ne eq).elim | exact (exz.ne eq.symm).elim |
            exact (eyz.ne eq).elim | exact (eyz.ne eq.symm).elim
  have rightContact (i : Fin 8) (hi : ¬i.val < 5) (j : Fin 5) :
      G.Adj (g i) (F.c j) ↔ RootContact t u i j := by
    rcases outside_cases i hi with rfl | rfl | rfl
    · rw [gx]
      exact (ht j).trans (by simp [RootContact])
    · rw [gy]
      exact (hu j).trans (by simp [RootContact])
    · rw [gz]
      simp [RootContact,hz.2 j]
  have nyx : ¬G.Adj y x := fun h => nxy h.symm
  have lift (i j : Fin 8) : G.Adj (g i) (g j) ↔ farRel t u i j := by
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · simpa only [g,farRel,dif_pos hi,dif_pos hj] using F.adj ⟨_,hi⟩ ⟨_,hj⟩
    · rw [farRel,dif_pos hi,dif_neg hj,show g i = F.c ⟨i.val,hi⟩ from dif_pos hi,G.adj_comm,
        rightContact j hj]
    · rw [farRel,dif_neg hi,dif_pos hj,show g j = F.c ⟨j.val,hj⟩ from dif_pos hj,
        rightContact i hi]
    · rcases outside_cases i hi with rfl | rfl | rfl <;>
        rcases outside_cases j hj with rfl | rfl | rfl
      all_goals simp [farRel,hi,hj,gx,gy,gz,exz,exz.symm,eyz,eyz.symm,nxy,
        nyx,G.loopless]
  have cert := checkFar t u
  cases he : farTable t u with
  | four i j p q =>
    have er : i ≠ j ∧ p ≠ q ∧ farRel t u i p ∧ farRel t u j p ∧
        farRel t u i q ∧ farRel t u j q := by
      simpa only [he,certTrue] using cert
    obtain ⟨nij,npq,ip,jp,iq,jq⟩ := er
    have contra := F.h4 _ _ _ _ (fun e => nij (inj e)) ((lift _ _).mpr ip)
      ((lift _ _).mpr jp) ((lift _ _).mpr iq) ((lift _ _).mpr jq)
    exact (npq (inj contra)).elim
  | path p =>
    have er : (∀ i j, p i = p j → i = j) ∧
        ∀ i j : Fin 7, i < j → (farRel t u (p i) (p j) ↔ i.val+1=j.val) := by
      simpa only [he,certTrue] using cert
    exact (no7 ⟨g ∘ p,inj.comp er.1,fun i j h => (lift _ _).trans (er.2 i j h)⟩).elim
  | hole6 c =>
    have er : (∀ i j, c i = c j → i = j) ∧
        ∀ i j : Fin 6, farRel t u (c i) (c j) ↔ Cyclic i j := by
      simpa only [he,certTrue] using cert
    exact Or.inl ⟨⟨g ∘ c,inj.comp er.1,fun i j => (lift _ _).trans (er.2 _ _)⟩⟩
  | hole7 c =>
    have er : (∀ i j, c i = c j → i = j) ∧
        ∀ i j : Fin 7, farRel t u (c i) (c j) ↔ Cyclic i j := by
      simpa only [he,certTrue] using cert
    exact Or.inr ⟨⟨g ∘ c,inj.comp er.1,fun i j => (lift _ _).trans (er.2 _ _)⟩⟩


theorem far_forces_hole (hc : G.Connected)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    (hmin : ∀ x, 2 ≤ localIndependence G x) {z : V} (hz : Far F z) :
    Nonempty (Hole G 6) ∨ Nonempty (Hole G 7) := by
  classical
  obtain ⟨A,hA,hC⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) z
  have pos := hmin z
  obtain ⟨x,hx,y,hy,hne⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have near (v : V) (ev : G.Adj z v) : Near F v := by
    have out : ∀ i, v ≠ F.c i := fun i he => hz.2 i (he ▸ ev)
    refine ⟨out,?_⟩
    apply Classical.byContradiction
    intro no
    have hFar : Far F v := ⟨out,fun i h => no ⟨i,h⟩⟩
    exact F.far_independent hc no7 hmin hz hFar ev
  exact F.far_pair_forces_hole (near x (hN x hx)) (near y (hN y hy)) hz hne
    (hI _ hx _ hy) (hN _ hx).symm (hN _ hy).symm no7

private lemma long_pent_arc : ∀ i j : Fin 5, i ≠ j → ¬pent i j →
    ∃ k l, [i,j,k,l].Nodup ∧ pent j k ∧ pent k l ∧ pent l i ∧
      ¬pent j l ∧ ¬pent i k := by decide

theorem different_singles_hole {x y : V} {i j : Fin 5}
    (hx : MakeOne F x i) (hy : MakeOne F y j) (ij : i ≠ j) (e : G.Adj x y) :
    Nonempty (Hole G 6) := by
  have ex := (hx.2 i).mpr rfl
  have ey := (hy.2 j).mpr rfl
  have nc : ¬pent i j := by
    intro h
    exact hy.1 i (F.h4 x (F.c j) y (F.c i) (hx.1 j) e ey.symm ex
      ((F.adj _ _).mpr h).symm)
  obtain ⟨k,l,hn,ek,el,ei,nl,nk⟩ := long_pent_arc i j ij nc
  have nd : [F.c i,F.c j,F.c k,F.c l].Nodup := by simpa using hn.map F.inj
  have ij' : F.c i ≠ F.c j := F.inj.ne ij
  have jk : j ≠ k := by
    intro h
    have n := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    exact n (by simp [h])
  have jl : j ≠ l := by
    intro h
    have n := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    exact n (by simp [h])
  have ik : i ≠ k := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have il : i ≠ l := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have kl : k ≠ l := by
    intro h
    have n := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
    exact n (by simp [h])
  let p : Fin 5 → V := ![x,y,F.c j,F.c k,F.c l]
  have hp : InducedPath G p := by
    constructor
    · apply List.nodup_ofFn.mp
      simp [p,List.ofFn_succ,e.ne,hx.1 j,hx.1 k,hx.1 l,hy.1 j,hy.1 k,hy.1 l,
        F.inj.ne jk,F.inj.ne jl,F.inj.ne kl]
    · intro u v huv
      have ajk := (F.adj _ _).mpr ek
      have akl := (F.adj _ _).mpr el
      have nxj : ¬G.Adj x (F.c j) := fun h => ij ((hx.2 j).mp h).symm
      have nxk : ¬G.Adj x (F.c k) := fun h => ik ((hx.2 k).mp h).symm
      have nxl : ¬G.Adj x (F.c l) := fun h => il ((hx.2 l).mp h).symm
      have nyk : ¬G.Adj y (F.c k) := fun h => jk ((hy.2 k).mp h).symm
      have nyl : ¬G.Adj y (F.c l) := fun h => jl ((hy.2 l).mp h).symm
      have njl : ¬G.Adj (F.c j) (F.c l) := fun h => nl ((F.adj _ _).mp h)
      fin_cases u <;> fin_cases v
      all_goals first | contradiction | exact iff_of_true e rfl | exact iff_of_true ey rfl |
        exact iff_of_true ajk rfl | exact iff_of_true akl rfl |
        exact iff_of_false nxj (by decide) | exact iff_of_false nxk (by decide) |
        exact iff_of_false nxl (by decide) | exact iff_of_false nyk (by decide) |
        exact iff_of_false nyl (by decide) | exact iff_of_false njl (by decide)
  have off (t : Fin 5) : F.c i ≠ p t := by
    fin_cases t
    · exact (hx.1 _).symm
    · exact (hy.1 _).symm
    · exact ij'
    · exact F.inj.ne ik
    · exact F.inj.ne il
  refine close_induced_path (m:=5) (by decide) hp (F.c i) off ?_ ?_ ?_
  · change G.Adj (F.c i) x
    exact ex.symm
  · change G.Adj (F.c i) (F.c l)
    exact ((F.adj _ _).mpr ei).symm
  · intro t h0 hm
    have not_y : ¬G.Adj (F.c i) y := fun h => ij ((hy.2 _).mp h.symm)
    have not_j : ¬G.Adj (F.c i) (F.c j) := fun h => nc ((F.adj _ _).mp h)
    have not_k : ¬G.Adj (F.c i) (F.c k) := fun h => nk ((F.adj _ _).mp h)
    fin_cases t
    · exact ((by decide : ¬ (0 < 0)) h0).elim
    · exact not_y
    · exact not_j
    · exact not_k
    · exact ((by decide : ¬(4+1 < 5)) hm).elim

#print axioms far_forces_hole
#print axioms different_singles_hole
end Frame
end Graffiti133FarPentagon
