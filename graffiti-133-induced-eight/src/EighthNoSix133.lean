import LocalDensity133
import RoundedBand133
import PentagonStructure133
import SixCycle133

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
universe u
variable {V : Type u} [Fintype V]

/-- No ordinary (not merely induced) six-cycle. -/
def NoSimpleSix (G : SimpleGraph V) : Prop :=
  ∀ a b c d e f, [a,b,c,d,e,f].Nodup →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → G.Adj f a → False

theorem max_local_set_with (G : SimpleGraph V) (h4 : FourCycleFree G)
    {v y : V} (hy : G.Adj v y) :
    ∃ A ∈ localIndependentSets G v, y ∈ A ∧ A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hAC⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  by_cases hyA : y ∈ A
  · exact ⟨A,hA,hyA,hAC⟩
  have max_of_insert {B : Finset V} (hB : B ⊆ A)
      (hNo : ∀ z ∈ B, ¬ G.Adj y z) : insert y B ∈ localIndependentSets G v := by
    apply Graffiti133Pentagon.PentagonFrame.memLocalSet.mpr
    constructor
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hy
      · exact hN _ (hB hz)
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with e | ha'
      · subst a
        rcases Finset.mem_insert.mp hb with e | hb'
        · subst b
          exact G.loopless _
        · exact hNo _ hb'
      · rcases Finset.mem_insert.mp hb with e | hb'
        · subst b
          exact fun h => hNo _ ha' h.symm
        · exact hI _ (hB ha') _ (hB hb')
  by_cases h : ∃ z ∈ A, G.Adj y z
  · obtain ⟨z,hz,hyz⟩ := h
    have hh : insert y (A.erase z) ∈ localIndependentSets G v :=
      max_of_insert (Finset.erase_subset _ _) (fun w hw hyw =>
        (Finset.mem_erase.mp hw).1
          (h4 v y w z hy.ne (hN _ (Finset.mem_erase.mp hw).2) hyw (hN _ hz) hyz))
    refine ⟨_,hh,Finset.mem_insert_self _ _,?_⟩
    rw [Finset.card_insert_of_not_mem (fun e => hyA (Finset.erase_subset _ _ e)),
      Finset.card_erase_add_one hz, hAC]
  · push_neg at h
    have hh := Finset.le_sup (f := Finset.card) (max_of_insert (B := A) (fun _ e => e) h)
    rw [Finset.card_insert_of_not_mem hyA, hAC] at hh
    change localIndependence G v + 1 ≤ localIndependence G v at hh
    exact (by omega : False).elim

private theorem nodup4 {f : Fin 7 → V} (hf : Function.Injective f) :
    [f 0,f 1,f 2,f 3].Nodup := by
  have h : [(0:Fin 7),1,2,3].Nodup := by decide
  simpa using h.map hf

private theorem nodup5 {f : Fin 7 → V} (hf : Function.Injective f) :
    [f 0,f 1,f 2,f 3,f 4].Nodup := by
  have h : [(0:Fin 7),1,2,3,4].Nodup := by decide
  simpa using h.map hf

/-- A terminal of local independence ≥3 on an induced P7 gives P8
when ordinary C4, C5 and C6 are forbidden. -/
theorem eighth_from_terminal_three {G : SimpleGraph V} (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (h6 : NoSimpleSix G)
    {f : Fin 7 → V} (hf : InducedPath G f) (hm : 3 ≤ localIndependence G (f 0)) :
    ∃ q : Fin 8 → V, InducedPath G q := by
  classical
  by_contra no
  have e (i j : Fin 7) (h : i.val+1=j.val) : G.Adj (f i) (f j) :=
    (hf.2 i j (by change i.val<j.val; omega)).mpr h
  have a01 := e 0 1 rfl
  have a12 := e 1 2 rfl
  have a23 := e 2 3 rfl
  have a34 := e 3 4 rfl
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
  have blocker {a : V} (ha : a∈R) : G.Adj a (f 5) ∨ G.Adj a (f 6) := by
    by_contra hh
    have nt (i : Fin 7) (hi : 0 < i.val) : ¬G.Adj a (f i) := by
      fin_cases i
      · change 0 < 0 at hi; omega
      · exact hI _ (Finset.mem_erase.mp ha).2 _ hOne
      · intro e'
        exact not1 ha (h4 (f 0) (f 2) a (f 1) (hf.1.ne (by decide)) (adj ha) e'.symm a01 a12.symm)
      · intro e'
        have hn : [a,f 0,f 1,f 2,f 3].Nodup := List.nodup_cons.mpr
          ⟨by simp [off ha],nodup4 hf.1⟩
        exact h5 _ _ _ _ _ hn (adj ha).symm a01 a12 a23 e'.symm
      · intro e'
        have hn : [a,f 0,f 1,f 2,f 3,f 4].Nodup := List.nodup_cons.mpr
          ⟨by simp [off ha],nodup5 hf.1⟩
        exact h6 _ _ _ _ _ _ hn (adj ha).symm a01 a12 a23 a34 e'.symm
      · exact fun h => hh (Or.inl h)
      · exact fun h => hh (Or.inr h)
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hf a (off ha) (adj ha).symm nt
    exact no ⟨q,hq⟩
  have same {i : Fin 7} (hi : (0:Fin 7)≠i) (ew : G.Adj w (f i)) (ez : G.Adj z (f i)) : False :=
    wz (h4 _ _ _ _ (hf.1.ne hi) (adj hw) ew.symm (adj hz) ez.symm)
  have next {a b : V} (ha : a∈R) (hb : b∈R) (ab : a≠b)
      (eA : G.Adj a (f 5)) (eB : G.Adj b (f 6)) : False := by
    have hn : [f 0,a,f 5,f 6,b].Nodup := by
      simp [Ne.symm (off ha 0), Ne.symm (off hb 0), off ha, Ne.symm (off hb 5),
        Ne.symm (off hb 6), ab, hf.1.ne (by decide : (0:Fin 7)≠5),
        hf.1.ne (by decide : (0:Fin 7)≠6), hf.1.ne (by decide : (5:Fin 7)≠6)]
    exact h5 _ _ _ _ _ hn (adj ha) eA (e 5 6 rfl) eB.symm (adj hb).symm
  rcases blocker hw with hw' | hw' <;> rcases blocker hz with hz' | hz'
  · exact same (by decide) hw' hz'
  · exact next hw hz wz hw' hz'
  · exact next hz hw wz.symm hz' hw'
  · exact same (by decide) hw' hz'

theorem P8_of_local_mean_four_no_five_six (G : SimpleGraph V) [Nonempty V]
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (h6 : NoSimpleSix G)
    (hmean : 4 ≤ averageLocal G) : ∃ f : Fin 8 → V, InducedPath G f := by
  classical
  apply lift_local_density_path 8 2 4 (by decide) (by decide) G h4
    (nat_density_of_le_average G 4 hmean)
  intro W _ _ J e he h4J hm _
  have h5J : NoSimpleFive133 J := by
    intro a b c d f nd ea eb ec ed ef
    exact h5 _ _ _ _ _ (by simpa using nd.map e.injective)
      ((he _ _).mp ea) ((he _ _).mp eb) ((he _ _).mp ec) ((he _ _).mp ed) ((he _ _).mp ef)
  have h6J : NoSimpleSix J := by
    intro a b c d f g nd ea eb ec ed ef eg
    exact h6 _ _ _ _ _ _ (by simpa using nd.map e.injective)
      ((he _ _).mp ea) ((he _ _).mp eb) ((he _ _).mp ec) ((he _ _).mp ed) ((he _ _).mp ef) ((he _ _).mp eg)
  obtain ⟨k,hk,f,hf⟩ := no_four_five_path_of_min_local J h4J h5J 3 (by decide) hm
  obtain ⟨g,hg⟩ := trim_path (by omega : 7 ≤ k) hf
  exact eighth_from_terminal_three h4J h5J h6J hg (hm (g 0))

#print axioms eighth_from_terminal_three
#print axioms P8_of_local_mean_four_no_five_six
end Graffiti133Eighth
