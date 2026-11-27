import EighthNoSix133

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open Graffiti133RevisitSix
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Anchor (G : SimpleGraph V) where
  p : Fin 7 → V
  hp : InducedPath G p
  w : V
  z : V
  nw : ∀ i, w ≠ p i
  nz : ∀ i, z ≠ p i
  wz : w ≠ z
  no : ¬G.Adj w z
  cW : ∀ i, G.Adj w (p i) ↔ i=0 ∨ i=4
  cZ : ∀ i, G.Adj z (p i) ↔ i=0 ∨ i=6

/-- If P8 is absent, the only possible blocking configuration at a
P7 endpoint with λ≥3 is this nine-vertex anchor. -/
theorem anchor_of_path7 {f : Fin 7 → V}
    (hf : InducedPath G f) (hm : 3 ≤ localIndependence G (f 0))
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (no : ¬∃ q : Fin 8 → V, InducedPath G q) : Nonempty (Anchor G) := by
  classical
  have e (i j : Fin 7) (h : i.val+1=j.val) : G.Adj (f i) (f j) :=
    (hf.2 i j (by change i.val<j.val; omega)).mpr h
  have a01 := e 0 1 rfl
  have a12 := e 1 2 rfl
  have a23 := e 2 3 rfl
  obtain ⟨A,hA,hOne,hAC⟩ := max_local_set_with G h4 a01
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let R := A.erase (f 1)
  have cb : 1 < R.card := by
    have c := (Finset.card_erase_add_one hOne).trans hAC
    change R.card+1=localIndependence G (f 0) at c
    omega
  obtain ⟨w,hw,z,hz,wz⟩ := Finset.one_lt_card.mp cb
  have adj {a : V} (ha : a∈R) : G.Adj (f 0) a := hN _ (Finset.mem_erase.mp ha).2
  have not1 {a : V} (ha : a∈R) : a ≠ f 1 := (Finset.mem_erase.mp ha).1
  have off {a : V} (ha : a∈R) (i : Fin 7) : a ≠ f i := by
    intro he
    by_cases hi : i=0
    · exact (adj ha).ne (he.trans (congrArg f hi)).symm
    have hib : (0:Fin 7) < i := Fin.pos_iff_ne_zero.mpr hi
    have q := (hf.2 _ _ hib).mp (he ▸ adj ha)
    have hi' : i=1 := Fin.ext q.symm
    exact not1 ha (he.trans (congrArg f hi'))
  have noShort {a : V} (ha : a ∈ R) (i : Fin 7) (hi : 0 < i.val) (h : i.val ≤ 3) :
      ¬G.Adj a (f i) := by
    have he : i=1 ∨ i=2 ∨ i=3 := by
      have q : i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      exact q.imp (fun h => Fin.ext h) (fun q => q.imp (fun h => Fin.ext h) (fun h => Fin.ext h))
    rcases he with rfl | rfl | rfl
    · exact hI _ (Finset.mem_erase.mp ha).2 _ hOne
    · intro e'
      exact not1 ha (h4 (f 0) (f 2) a (f 1) (hf.1.ne (by decide)) (adj ha) e'.symm a01 a12.symm)
    · intro e'
      have nd : [(0:Fin 7),1,2,3].Nodup := by decide
      have nd' : [f 0,f 1,f 2,f 3].Nodup := by simpa using nd.map hf.1
      have hn : [a,f 0,f 1,f 2,f 3].Nodup := List.nodup_cons.mpr ⟨by simp [off ha],nd'⟩
      exact h5 _ _ _ _ _ hn (adj ha).symm a01 a12 a23 e'.symm
  have blocker {a : V} (ha : a∈R) : ∃ i : Fin 7, 4 ≤ i.val ∧ G.Adj a (f i) := by
    apply Classical.byContradiction
    intro hh
    have nt (i : Fin 7) (hi : 0 < i.val) : ¬G.Adj a (f i) := by
      by_cases h : 4 ≤ i.val
      · exact fun z => hh ⟨i,h,z⟩
      · exact noShort ha i hi (by omega)
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hf a (off ha) (adj ha).symm nt
    exact no ⟨q,hq⟩
  have same {a b : V} (ha : a∈R) (hb : b∈R) (ab : a≠b)
      {i : Fin 7} (hi : (0:Fin 7)≠i) (eA : G.Adj a (f i)) (eB : G.Adj b (f i)) : False :=
    ab (h4 _ _ _ _ (hf.1.ne hi) (adj ha) eA.symm (adj hb) eB.symm)
  have next {a b : V} (ha : a∈R) (hb : b∈R) (ab : a≠b)
      {i j : Fin 7} (ni : (0:Fin 7) ≠ i) (nj : (0:Fin 7) ≠ j)
      (ij : i.val+1=j.val) (eA : G.Adj a (f i)) (eB : G.Adj b (f j)) : False := by
    have hh := e i j ij
    have hn : [f 0,a,f i,f j,b].Nodup := by
      simp [Ne.symm (off ha 0), Ne.symm (off hb 0), off ha, Ne.symm (off hb i),
        Ne.symm (off hb j), ab, hf.1.ne ni,hf.1.ne nj,hh.ne]
    exact h5 _ _ _ _ _ hn (adj ha) eA hh eB.symm (adj hb).symm
  have specific {a b : V} (ha : a∈R) (hb : b∈R) (ab : a≠b)
      (h4a : G.Adj a (f 4)) (h6b : G.Adj b (f 6)) : Nonempty (Anchor G) := by
    have a5 : ¬G.Adj a (f 5) := fun h => next ha hb ab (by decide) (by decide) (by decide) h h6b
    have a6 : ¬G.Adj a (f 6) := fun h => same ha hb ab (by decide) h h6b
    have b4 : ¬G.Adj b (f 4) := fun h => same ha hb ab (by decide) h4a h
    have b5 : ¬G.Adj b (f 5) := fun h => next ha hb ab (by decide) (by decide) (by decide) h4a h
    refine ⟨⟨f,hf,a,b,off ha,off hb,ab,hI _ (Finset.mem_erase.mp ha).2 _ (Finset.mem_erase.mp hb).2,?_,?_⟩⟩
    · intro i
      fin_cases i
      · simp [(adj ha).symm]
      · have h := noShort ha 1 (by decide) (by decide); simp [h]
      · have h := noShort ha 2 (by decide) (by decide); simp [h]
      · have h := noShort ha 3 (by decide) (by decide); simp [h]
      · simp [h4a]
      · simp [a5]
      · simp [a6]
    · intro i
      fin_cases i
      · simp [(adj hb).symm]
      · have h := noShort hb 1 (by decide) (by decide); simp [h]
      · have h := noShort hb 2 (by decide) (by decide); simp [h]
      · have h := noShort hb 3 (by decide) (by decide); simp [h]
      · simp [b4]
      · simp [b5]
      · simp [h6b]
  obtain ⟨i,hi,eI⟩ := blocker hw
  obtain ⟨j,hj,eJ⟩ := blocker hz
  have ni : (0:Fin 7)≠i := by intro h; rw [←h] at hi; contradiction
  have nj : (0:Fin 7)≠j := by intro h; rw [←h] at hj; contradiction
  have hne : i.val≠j.val := fun h => same hw hz wz ni eI (Fin.ext h |>.symm ▸ eJ)
  have n1 : i.val+1≠j.val := fun h => next hw hz wz ni nj h eI eJ
  have n2 : j.val+1≠i.val := fun h => next hz hw wz.symm nj ni h eJ eI
  rcases (show (i.val=4 ∧ j.val=6) ∨ (i.val=6 ∧ j.val=4) by
    have := i.isLt; have := j.isLt; omega) with ⟨a,b⟩ | ⟨a,b⟩
  · have ai : i=(4:Fin 7) := Fin.ext a
    have bj : j=(6:Fin 7) := Fin.ext b
    exact specific hw hz wz (ai ▸ eI) (bj ▸ eJ)
  · have ai : i=(6:Fin 7) := Fin.ext a
    have bj : j=(4:Fin 7) := Fin.ext b
    exact specific hz hw wz.symm (bj ▸ eJ) (ai ▸ eI)

#print axioms anchor_of_path7
end Graffiti133Eighth
