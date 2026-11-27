import P8Anchor133
import P8HeawoodCertBase

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133P8Heawood Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}

structure Model (G : SimpleGraph V) (R : Fin n → Fin n → Prop) where
  f : Fin n → V
  inj : Function.Injective f
  adj (i j) : R i j ↔ G.Adj (f i) (f j)

namespace Model
variable {R : Fin n → Fin n → Prop} (M : Model G R)

def Fresh (v : V) := ∀ i, v ≠ M.f i

noncomputable def contacts (v : V) (i : Fin n) : Bool :=
  @decide (G.Adj v (M.f i)) (Classical.propDecidable _)

@[simp] theorem contacts_true (v : V) (i : Fin n) :
    M.contacts v i = true ↔ G.Adj v (M.f i) := by simp [contacts]

theorem contacts_false (v : V) (i : Fin n) :
    M.contacts v i = false ↔ ¬ G.Adj v (M.f i) := by
  exact Bool.eq_false_iff.trans (not_congr (M.contacts_true v i))

include M in
theorem good (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (h8 : ¬∃ p : Fin 8 → V, InducedPath G p) : Good R where
  h4 := fun i j a b hij hab ha ha' hb hb' => hab (M.inj
    (h4 _ _ _ _ (M.inj.ne hij) ((M.adj _ _).mp ha) ((M.adj _ _).mp ha')
      ((M.adj _ _).mp hb) ((M.adj _ _).mp hb')))
  h5 := by
    intro p hp ed
    have inj : Function.Injective (M.f ∘ p) := M.inj.comp (fun {_ _} => hp _ _)
    have hn : [M.f (p 0), M.f (p 1), M.f (p 2), M.f (p 3), M.f (p 4)].Nodup := by
      simpa [List.ofFn_succ] using List.nodup_ofFn.mpr inj
    exact h5 _ _ _ _ _ hn ((M.adj ..).mp (ed 0)) ((M.adj ..).mp (ed 1))
      ((M.adj ..).mp (ed 2)) ((M.adj ..).mp (ed 3)) ((M.adj ..).mp (ed 4))
  h8 := by
    intro p hp edges
    exact h8 ⟨M.f ∘ p, M.inj.comp (fun {_ _} => hp _ _),fun i j h =>
      (M.adj _ _).symm.trans (edges _ _ h)⟩

def extend (v : V) (hn : M.Fresh v) {B : Fin n → Bool}
    (hB : ∀ i, B i = true ↔ G.Adj v (M.f i)) : Model G (ext R B) where
  f := Fin.lastCases v M.f
  inj := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h
      exact (hn _ (by simpa using h)).elim
    · intro h
      exact (hn _ (by simpa using h.symm)).elim
    · intro h
      exact congrArg Fin.castSucc (M.inj (by simpa using h))
  adj := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [G.loopless]
    · simpa using hB j
    · simpa only [ext_from_old,Fin.lastCases_castSucc,Fin.lastCases_last,G.adj_comm] using hB i
    · simpa using M.adj i j

@[simp] theorem extend_f_old (v : V) (hn : M.Fresh v) {B : Fin n → Bool}
    (hB : ∀ i, B i = true ↔ G.Adj v (M.f i)) (i : Fin n) :
    (M.extend v hn hB).f i.castSucc = M.f i := by simp [extend]

@[simp] theorem extend_f_new (v : V) (hn : M.Fresh v) {B : Fin n → Bool}
    (hB : ∀ i, B i = true ↔ G.Adj v (M.f i)) :
    (M.extend v hn hB).f (Fin.last n) = v := by simp [extend]

def changeRel {S : Fin n → Fin n → Prop} (h : ∀ i j, S i j ↔ R i j) : Model G S :=
  ⟨M.f,M.inj,fun i j => (h i j).trans (M.adj i j)⟩

theorem exists_fresh_neighbor (i a b : Fin n)
    (cap : ∀ j, R i j → j = a ∨ j = b) (hm : 3 ≤ localIndependence G (M.f i)) :
    ∃ v, M.Fresh v ∧ G.Adj v (M.f i) := by
  classical
  apply Classical.byContradiction
  intro bad
  obtain ⟨A,hA,hC⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) (M.f i)
  have sub : A ⊆ {M.f a,M.f b} := by
    intro v hv
    have e := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 v hv
    have ex : ∃ j, v = M.f j := by
      by_contra h
      exact bad ⟨v,fun j eq => h ⟨j,eq⟩,e.symm⟩
    obtain ⟨j,rfl⟩ := ex
    have := cap j ((M.adj ..).mpr e)
    rcases this with rfl | rfl <;> simp
  have hc := (Finset.card_le_card sub).trans
    (show ({M.f a,M.f b} : Finset V).card ≤ 2 from (Finset.card_insert_le _ _).trans (by simp))
  omega

theorem covers_if_closed (hc : G.Connected) (root : Fin n)
    (closed : ∀ v, M.Fresh v → ∀ i, ¬G.Adj v (M.f i)) : Function.Surjective M.f := by
  classical
  have step {a b : V} (e : G.Adj a b) (ha : ∃ i, M.f i = a) : ∃ i, M.f i = b := by
    apply Classical.byContradiction
    intro no
    obtain ⟨i,rfl⟩ := ha
    exact closed b (fun j h => no ⟨j,h.symm⟩) i e.symm
  have aux {a b : V} (w : G.Walk a b) (ha : ∃ i, M.f i=a) : ∃ i, M.f i=b := by
    induction w with
    | nil => exact ha
    | cons e w ih => exact ih (step e ha)
  intro v
  obtain ⟨w⟩ := hc (M.f root) v
  exact aux w ⟨root,rfl⟩
end Model

private theorem path_rel {f : Fin 7 → V} (hf : InducedPath G f) (i j : Fin 7) :
    G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  rcases lt_trichotomy i j with ht | he | ht
  · rw [hf.2 i j ht]
    change i.val < j.val at ht
    exact ⟨Or.inl,fun h => h.resolve_right (by omega)⟩
  · subst j
    simp [G.loopless]
  · rw [G.adj_comm,hf.2 j i ht]
    change j.val < i.val at ht
    exact ⟨Or.inr,fun h => h.resolve_left (by omega)⟩

def Anchor.model (A : Graffiti133Eighth.Anchor G) : Model G Graffiti133P8Heawood.Anchor where
  f := Fin.lastCases A.z (Fin.lastCases A.w A.p)
  inj := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _; rfl
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact (A.wz (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h.symm)).elim
        · intro h; exact (A.nz _ (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h)).elim
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · intro h; exact (A.wz (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h)).elim
        · intro h; exact (A.nz _ (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h.symm)).elim
      · refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _; rfl
        · intro h; exact (A.nw _ (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h)).elim
        · intro h; exact (A.nw _ (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h.symm)).elim
        · intro h
          exact congrArg (fun k : Fin 7 => k.castSucc.castSucc) (A.hp.1 (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using h))
  adj := by
    have pp : ∀ i j : Fin 7, Graffiti133P8Heawood.Anchor i.castSucc.castSucc j.castSucc.castSucc ↔
        i.val+1=j.val ∨ j.val+1=i.val := by decide
    have u : ∀ i : Fin 7, Graffiti133P8Heawood.Anchor ((Fin.last 7).castSucc) i.castSucc.castSucc ↔
        i=0 ∨ i=4 := by decide
    have u' : ∀ i : Fin 7, Graffiti133P8Heawood.Anchor i.castSucc.castSucc ((Fin.last 7).castSucc) ↔
        i=0 ∨ i=4 := by decide
    have v : ∀ i : Fin 7, Graffiti133P8Heawood.Anchor (Fin.last 8) i.castSucc.castSucc ↔
        i=0 ∨ i=6 := by decide
    have v' : ∀ i : Fin 7, Graffiti133P8Heawood.Anchor i.castSucc.castSucc (Fin.last 8) ↔
        i=0 ∨ i=6 := by decide
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
        exact iff_of_false (by decide) (G.loopless A.z)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · have no : ¬G.Adj A.z A.w := fun e => A.no e.symm
          simpa only [Fin.lastCases_castSucc,Fin.lastCases_last,no,iff_false] using (show ¬Graffiti133P8Heawood.Anchor (Fin.last 8) (Fin.last 7).castSucc by decide)
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using (v j).trans (A.cZ j).symm
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last,A.no,iff_false] using (show ¬Graffiti133P8Heawood.Anchor (Fin.last 7).castSucc (Fin.last 8) by decide)
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last,G.adj_comm] using (v' i).trans (A.cZ i).symm
      · refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
          exact iff_of_false (by decide) (G.loopless A.w)
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using (u j).trans (A.cW j).symm
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last,G.adj_comm] using (u' i).trans (A.cW i).symm
        · simpa using (pp i j).trans (path_rel A.hp i j).symm

#print axioms Model.good
#print axioms Anchor.model
end Graffiti133Eighth
