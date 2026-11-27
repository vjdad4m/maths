import SeventhNoFive133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Cycle adjacency written via natural indices, including the closing edge. -/
def Cyclic {n : ℕ} (i j : Fin n) : Prop :=
  i.val+1=j.val ∨ j.val+1=i.val ∨
    (i.val=0 ∧ j.val+1=n) ∨ (j.val=0 ∧ i.val+1=n)

instance {n : ℕ} : DecidableRel (@Cyclic n) := by
  intro i j
  unfold Cyclic
  infer_instance

theorem cyclic_symm {n : ℕ} (i j : Fin n) : Cyclic i j ↔ Cyclic j i := by
  unfold Cyclic
  tauto

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def Outside {n : ℕ} (c : Fin n → V) (x : V) : Prop := ∀ i, x ≠ c i

structure Hole (G : SimpleGraph V) (n : ℕ) where
  c : Fin n → V
  inj : Function.Injective c
  adj : ∀ i j, G.Adj (c i) (c j) ↔ Cyclic i j

theorem close_induced_path {m : ℕ} (hm : 3 ≤ m) {p : Fin m → V}
    (hp : InducedPath G p) (w : V) (hw : ∀ i, w ≠ p i)
    (h0 : G.Adj w (p ⟨0,by omega⟩)) (hLast : G.Adj w (p ⟨m-1,by omega⟩))
    (hmiddle : ∀ i : Fin m, 0 < i.val → i.val+1 < m → ¬G.Adj w (p i)) :
    Nonempty (Hole G (m+1)) := by
  let c (i : Fin (m+1)) := if hi : i.val < m then p ⟨i.val,hi⟩ else w
  have cP (i : Fin m) : c i.castSucc = p i := by simp [c,i.isLt]
  have cW : c (Fin.last m) = w := by simp [c]
  have other (i : Fin (m+1)) : (∃ a : Fin m, i = a.castSucc) ∨ i = Fin.last m := by
    by_cases hi : i.val < m
    · exact Or.inl ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    · exact Or.inr (Fin.ext (by change i.val = m; have := i.isLt; omega))
  have inj : Function.Injective c := by
    intro i j he
    rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
    · rw [cP,cP] at he
      exact congrArg Fin.castSucc (hp.1 he)
    · rw [cP,cW] at he
      exact (hw _ he.symm).elim
    · rw [cW,cP] at he
      exact (hw _ he).elim
    · rfl
  have interior (a b : Fin m) : G.Adj (p a) (p b) ↔ Cyclic a.castSucc b.castSucc := by
    have aa := a.isLt
    have bb := b.isLt
    change G.Adj (p a) (p b) ↔ a.val+1=b.val ∨ b.val+1=a.val ∨
      (a.val=0 ∧ b.val+1=m+1) ∨ (b.val=0 ∧ a.val+1=m+1)
    rcases lt_trichotomy a b with lt | e | gt
    · rw [hp.2 a b lt]
      change a.val < b.val at lt
      omega
    · subst b
      simp [G.loopless]
      omega
    · rw [G.adj_comm,hp.2 b a gt]
      change b.val < a.val at gt
      omega
  have ext (i : Fin m) : G.Adj (p i) w ↔ Cyclic i.castSucc (Fin.last m) := by
    change G.Adj (p i) w ↔ i.val+1=m ∨ m+1=i.val ∨
      (i.val=0 ∧ m+1=m+1) ∨ (m=0 ∧ i.val+1=m+1)
    constructor
    · intro e
      have := i.isLt
      by_cases h : i.val = 0
      · exact Or.inr (Or.inr (Or.inl ⟨h,rfl⟩))
      · by_cases e' : i.val+1=m
        · exact Or.inl e'
        · exact (hmiddle i (by omega) (by omega) e.symm).elim
    · intro h
      have hi := i.isLt
      have h' : i.val=0 ∨ i.val=m-1 := by omega
      rcases h' with h' | h'
      · have eq : i = ⟨0,by omega⟩ := Fin.ext h'
        exact eq ▸ h0.symm
      · have eq : i = ⟨m-1,by omega⟩ := Fin.ext h'
        exact eq ▸ hLast.symm
  refine ⟨⟨c,inj,?_⟩⟩
  intro i j
  rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
  · rw [cP,cP]
    exact interior a b
  · rw [cP,cW]
    exact ext a
  · rw [cW,cP,G.adj_comm,cyclic_symm]
    exact ext b
  · rw [cW]
    have hg : ¬ Cyclic (Fin.last m) (Fin.last m) := by
      change ¬(m+1=m ∨ m+1=m ∨ (m=0 ∧ m+1=m+1) ∨ (m=0 ∧ m+1=m+1))
      omega
    exact iff_of_false (G.loopless _) hg

/-- A certification interface for finite cyclic contact computations: the
resulting induced path starts at the attached vertex and stays in the cycle
thereafter. -/
def SpokeRel {n : ℕ} (b : Fin n → Bool) (i j : Fin (n+1)) : Prop :=
  if hi : i.val < n then
    if hj : j.val < n then Cyclic ⟨i.val,hi⟩ ⟨j.val,hj⟩ else b ⟨i.val,hi⟩=true
  else if hj : j.val < n then b ⟨j.val,hj⟩=true else False

instance {n : ℕ} (b : Fin n → Bool) : DecidableRel (SpokeRel b) := by
  intro i j
  unfold SpokeRel
  split <;> split <;> infer_instance

theorem lift_spoke {n : ℕ} (hn : 0 < n) (H : Hole G n)
    (x : V) (hx : Outside H.c x) {b : Fin n → Bool}
    (hb : ∀ i, b i = true ↔ G.Adj x (H.c i))
    (path : Fin n → Fin (n+1)) (inj : Function.Injective path)
    (hs : ∀ i j : Fin n, i < j → (SpokeRel b (path i) (path j) ↔ i.val+1=j.val))
    (head : path ⟨0,hn⟩ = Fin.last n)
    (tail : ∀ i, 0 < i.val → (path i).val < n) :
    ∃ p : Fin n → V, InducedPath G p ∧ p ⟨0,hn⟩ = x ∧
      ∀ i, 0 < i.val → ∃ j, p i = H.c j := by
  let g (r : Fin (n+1)) : V := if hr : r.val < n then H.c ⟨r.val,hr⟩ else x
  have gLast : g (Fin.last n) = x := by simp [g]
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < n <;> by_cases hB : b.val < n
    · have he := H.inj (show H.c ⟨a.val,hA⟩ = H.c ⟨b.val,hB⟩ by
        simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun z : Fin n => z.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin (n+1)) : G.Adj (g a) (g q) ↔ SpokeRel b a q := by
    by_cases hA : a.val < n <;> by_cases hQ : q.val < n
    · simpa only [g,SpokeRel,dif_pos hA,dif_pos hQ] using H.adj ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,SpokeRel,dif_pos hA,dif_neg hQ,G.adj_comm] using (hb ⟨a.val,hA⟩).symm
    · simpa only [g,SpokeRel,dif_neg hA,dif_pos hQ] using (hb ⟨q.val,hQ⟩).symm
    · simp [g,SpokeRel,hA,hQ,G.loopless]
  refine ⟨g ∘ path,⟨ginj.comp inj,fun a q he => (hrel _ _).trans (hs a q he)⟩,
    ?_,?_⟩
  · change g (path ⟨0,hn⟩) = x
    rw [head,gLast]
  · intro i hi
    exact ⟨⟨_,tail i hi⟩,dif_pos (tail i hi)⟩

private lemma chain6 : ∀ i : Fin 6, Cyclic i (i+1) ∧
    Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by decide
private lemma chain7 : ∀ i : Fin 7, Cyclic i (i+1) ∧
    Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by decide
private lemma inds6 : ∀ i : Fin 6, i≠i+2 ∧ [i,i+1,i+2,i+3].Nodup := by decide
private lemma inds7 : ∀ i : Fin 7, i≠i+2 ∧ [i,i+1,i+2,i+3].Nodup := by decide

/-- If the cycle has order six or seven, the first three successive
contacts give forbidden short cycles at separations two and three. -/
theorem no_spoke_offset {n : ℕ} [NeZero n]
    (hn : n = 6 ∨ n = 7) (H : Hole G n) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (x : V) (hx : Outside H.c x) (i : Fin n) (hi : G.Adj x (H.c i)) :
    ¬G.Adj x (H.c (i+2)) ∧ ¬G.Adj x (H.c (i+3)) := by
  have chain (i : Fin n) : Cyclic i (i+1) ∧ Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by
    rcases hn with rfl | rfl
    · exact chain6 i
    · exact chain7 i
  have steps : i ≠ i+2 ∧ [i,i+1,i+2,i+3].Nodup := by
    rcases hn with rfl | rfl
    · exact inds6 i
    · exact inds7 i
  obtain ⟨e1,e2,e3⟩ := chain i
  constructor
  · intro e
    exact hx _ (h4 (H.c i) (H.c (i+2)) x (H.c (i+1))
      (fun eq => steps.1 (H.inj eq)) hi.symm e.symm
      ((H.adj _ _).mpr e1) ((H.adj _ _).mpr e2).symm)
  · intro e
    have nod : [x,H.c i,H.c (i+1),H.c (i+2),H.c (i+3)].Nodup := by
      apply List.nodup_cons.mpr
      exact ⟨by simp [hx i,hx (i+1),hx (i+2),hx (i+3)],by simpa using steps.2.map H.inj⟩
    exact h5 _ _ _ _ _ nod hi ((H.adj _ _).mpr e1) ((H.adj _ _).mpr e2)
      ((H.adj _ _).mpr e3) e.symm

private def spokePath6 (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6, i.castSucc, (i + (if positive then 1 else 5)).castSucc,
    (i + (if positive then 2 else 4)).castSucc, (i + 3).castSucc,
    (i + (if positive then 4 else 2)).castSucc]

private def spokePath7 (i : Fin 7) (positive : Bool) : Fin 7 → Fin 8 :=
  ![7, i.castSucc, (i + (if positive then 1 else 6)).castSucc,
    (i + (if positive then 2 else 5)).castSucc, (i + (if positive then 3 else 4)).castSucc,
    (i + (if positive then 4 else 3)).castSucc, (i + (if positive then 5 else 2)).castSucc]

private lemma spoke6 : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false ∧ b (i+3) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ a c : Fin 6, spokePath6 i pos a = spokePath6 i pos c → a=c) ∧
      (∀ a c : Fin 6, a<c → (SpokeRel b (spokePath6 i pos a) (spokePath6 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 6, 0<a.val → (spokePath6 i pos a).val < 6) := by decide

private lemma spoke7 : ∀ b : Fin 7 → Bool,
    (∀ i, b i = true → b (i+2) = false ∧ b (i+3) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ a c : Fin 7, spokePath7 i pos a = spokePath7 i pos c → a=c) ∧
      (∀ a c : Fin 7, a<c → (SpokeRel b (spokePath7 i pos a) (spokePath7 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 7, 0<a.val → (spokePath7 i pos a).val < 7) := by decide

theorem extend_hole_no_five {n : ℕ} [NeZero n]
    (hn : n = 6 ∨ n = 7) (H : Hole G n) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (x : V) (hx : Outside H.c x) (ha : ∃ i, G.Adj x (H.c i)) :
    ∃ p : Fin n → V, InducedPath G p ∧ p ⟨0,NeZero.pos n⟩ = x ∧
      ∀ i, 0 < i.val → ∃ j, p i = H.c j := by
  classical
  let b : Fin n → Bool := fun i => decide (G.Adj x (H.c i))
  have bh (i : Fin n) : b i=true ↔ G.Adj x (H.c i) := by simp [b]
  have hs (i : Fin n) (hi : b i=true) : b (i+2)=false ∧ b (i+3)=false := by
    have hh := no_spoke_offset hn H h4 h5 x hx i ((bh i).mp hi)
    constructor
    · cases he : b (i+2)
      · rfl
      · exact (hh.1 ((bh _).mp he)).elim
    · cases he : b (i+3)
      · rfl
      · exact (hh.2 ((bh _).mp he)).elim
  have some : ∃ i, b i = true := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,(bh _).mpr hi⟩
  rcases hn with rfl | rfl
  · obtain ⟨i,pos,inj,e,tail⟩ := spoke6 b hs some
    exact lift_spoke (by decide) H x hx bh (spokePath6 i pos) inj e rfl tail
  · obtain ⟨i,pos,inj,e,tail⟩ := spoke7 b hs some
    exact lift_spoke (by decide) H x hx bh (spokePath7 i pos) inj e rfl tail

#print axioms extend_hole_no_five
end Graffiti133NoFive
