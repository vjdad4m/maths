import CambySwap133

namespace Graffiti133Camby
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133RevisitSix Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def Window (S K : Finset V) {n : ℕ} (f : Fin n → V) : Prop :=
  (∀ x, x∈S ↔ x∈K ∨ ∃ i, f i=x) ∧ ∀ i, f i∉K

private def Gap (G : SimpleGraph V) (K : Finset V) {n : ℕ} (f : Fin n → V) (k : ℕ) : Prop :=
  ∀ i : Fin n, i.val<k → ∀ x∈K, ¬ G.Adj (f i) x

private theorem slide {n k : ℕ} (hn : 2≤n) {S K : Finset V} {f : Fin n → V}
    (hm : MinimalSize G S) (hf : InducedPath G f) (hw : Window S K f)
    (hg : Gap G K f k) (no : NoPath G (n+2)) :
    ∃ (T : Finset V) (q : Fin n → V), MinimalSize G T ∧ InducedPath G q ∧ Window T K q ∧ Gap G K q (k+1) := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨n-1,by omega⟩
  have hi : Inside S f := fun i => (hw.1 _).2 (Or.inr ⟨i,rfl⟩)
  have no' : NoPath G ((n+1)+1) := no
  obtain ⟨y,hy⟩ := private_first hn hm hf hi (no_shorter_inside (n := n+1) (by omega) hm no')
  change PrivateAt G S (f a) y at hy
  obtain ⟨p,hp,hhead,htail⟩ := prepend_induced_with_positions (by omega) hf y
    (fun i e => hy.1 (e.symm ▸ hi i)) hy.2.1
    (fun i hi0 => hy.2.2 _ (hi i) (hf.1.ne (fun eq => by
      have ee := congrArg Fin.val eq
      change i.val=0 at ee
      omega)))
  let q : Fin n → V := fun i => p i.castSucc
  have hq : InducedPath G q := ⟨fun i j e => Fin.ext (congrArg (fun x : Fin (n+1) => x.val) (hp.1 e)),fun i j h => hp.2 i.castSucc j.castSucc h⟩
  have qzero : q a=y := hhead
  have qtail (i : Fin n) (h : 0 < i.val) : q i=f ⟨i.val-1,by omega⟩ :=
    htail i.castSucc h
  let T := insert y (S.erase (f b))
  refine ⟨T,q,swap_tip hn hm hf hi hy no,hq,⟨?_,?_⟩,?_⟩
  · intro x
    have keep : ∀ i : Fin n, i≠b → ∃ j : Fin n, q j=f i := by
      intro i ne
      have hn' : i.val+1<n := by
        by_contra! hh
        apply ne
        apply Fin.ext
        change i.val=n-1
        omega
      let j : Fin n := ⟨i.val+1,hn'⟩
      refine ⟨j,?_⟩
      rw [qtail j (by change 0 < i.val+1; omega)]
      congr 1
    have inT : ∀ j : Fin n, q j∈T := by
      intro j
      by_cases h : j.val=0
      · have e : j=a := Fin.ext h
        rw [e,qzero]
        exact Finset.mem_insert_self _ _
      · have hpos : 0 < j.val := by omega
        rw [qtail j hpos]
        apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨hf.1.ne (fun e => ?_),hi _⟩
        have ee := congrArg Fin.val e
        change j.val-1=n-1 at ee
        omega
    constructor
    · intro h
      rcases Finset.mem_insert.mp h with e|e
      · exact Or.inr ⟨a,qzero.trans e.symm⟩
      · have ge := Finset.mem_erase.mp e
        rcases (hw.1 x).mp ge.2 with hK|⟨i,eq⟩
        · exact Or.inl hK
        · have ne : i≠b := fun e => ge.1 (eq.symm.trans (congrArg f e))
          obtain ⟨j,ej⟩ := keep i ne
          exact Or.inr ⟨j,ej.trans eq⟩
    · rintro (hh|⟨j,rfl⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun e => hw.2 b (e ▸ hh), (hw.1 x).mpr (Or.inl hh)⟩)
      · exact inT j
  · intro i hmem
    by_cases hi0 : i.val=0
    · have e : i=a := Fin.ext hi0
      rw [e,qzero] at hmem
      exact hy.1 ((hw.1 y).mpr (Or.inl hmem))
    · rw [qtail i (by omega)] at hmem
      exact hw.2 _ hmem
  · intro i hiK x hx
    by_cases hi0 : i.val=0
    · have e : i=a := Fin.ext hi0
      rw [e,qzero]
      exact hy.2.2 _ ((hw.1 x).mpr (Or.inl hx)) (fun e => hw.2 a (e ▸ hx))
    · rw [qtail i (by omega)]
      exact hg _ (by simp; omega) x hx

private theorem run_slides {n : ℕ} (hn : 2≤n) {S K : Finset V} {f : Fin n → V}
    (hm : MinimalSize G S) (hf : InducedPath G f) (hw : Window S K f)
    (no : NoPath G (n+2)) (k : ℕ) (hk : k≤n) :
    ∃ (T : Finset V) (q : Fin n → V),
      MinimalSize G T ∧ InducedPath G q ∧ Window T K q ∧ Gap G K q k := by
  induction k with
  | zero => exact ⟨S,f,hm,hf,hw,fun i hi => (Nat.not_lt_zero i.val hi).elim⟩
  | succ k ih =>
    obtain ⟨T,q,hT,hq,hW,hG⟩ := ih (by omega)
    exact slide hn hT hq hW hG no

private theorem all_gap {n : ℕ} (hn : 2≤n) {T K : Finset V} {q : Fin n → V}
    (hT : CD G T) (hw : Window T K q) (hg : Gap G K q n) : K=∅ := by
  let a : Fin n := ⟨0,by omega⟩
  let u : (T : Set V) := ⟨q a,(hw.1 _).mpr (Or.inr ⟨a,rfl⟩)⟩
  have prop : ∀ {s t : (T : Set V)}, (G.induce (T : Set V)).Walk s t →
      (∃ i,q i=s.val) → ∃ i,q i=t.val := by
    intro s t p
    induction p with
    | nil => exact id
    | @cons s t r e p ih =>
      rintro ⟨i,eq⟩
      apply ih
      rcases (hw.1 _).mp t.property with hv|hv
      · have edge : G.Adj s.val t.val := e
        exact (hg i i.isLt _ hv (eq.symm ▸ edge)).elim
      · exact hv
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  let v : (T : Set V) := ⟨x,(hw.1 _).mpr (Or.inl hx)⟩
  obtain ⟨p⟩ := hT.1 u v
  obtain ⟨i,eq⟩ := prop p ⟨a,rfl⟩
  exact hw.2 i (eq.symm ▸ hx)

theorem connected_domination_decomposition (G : SimpleGraph V) (hc : G.Connected)
    (n : ℕ) (hn : 2≤n) (no : NoPath G (n+2)) :
    (∃ S, CD G S ∧ NoPathIn G S n) ∨
      ∃ H : Hole G (n+2), ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i) := by
  classical
  obtain ⟨S,hm⟩ := exists_minimalSize hc
  by_cases hs : NoPathIn G S n
  · exact Or.inl ⟨S,hm.1,hs⟩
  · obtain ⟨f,hf,hi⟩ := Classical.not_not.mp hs
    let K := S.filter (fun x => ¬∃ i, f i=x)
    have hw : Window S K f := by
      refine ⟨?_,?_⟩
      · intro x
        constructor
        · intro hx
          by_cases h : ∃ i,f i=x
          · exact Or.inr h
          · exact Or.inl (Finset.mem_filter.mpr ⟨hx,h⟩)
        · rintro (h|⟨i,rfl⟩)
          · exact (Finset.mem_filter.mp h).1
          · exact hi i
      · exact fun i h => (Finset.mem_filter.mp h).2 ⟨i,rfl⟩
    obtain ⟨T,q,hT,_,hW,hG⟩ := run_slides hn hm hf hw no n (le_refl _)
    have empty := all_gap hn hT.1 hW hG
    have spans : ∀ x∈S, ∃ i,f i=x := by
      intro x hx
      simpa [empty] using (hw.1 x).mp hx
    have no' := no_shorter_inside (n := n+1) (by omega) hm no
    obtain ⟨y,hy⟩ := private_first hn hm hf hi no'
    obtain ⟨z,hz⟩ := private_last hn hm hf hi no'
    obtain ⟨H,hcarry⟩ := cycle_of_private_tips hn hf hi hy hz no
    have carry : ∀ x∈S, ∃ j,H.c j=x := fun x hx => by
      obtain ⟨i,ei⟩ := spans x hx
      obtain ⟨j,ej⟩ := hcarry i
      exact ⟨j,ej.trans ei⟩
    refine Or.inr ⟨H,fun x hx => ?_⟩
    rcases hm.1.2 x with h|⟨v,hv,e⟩
    · obtain ⟨j,hj⟩ := carry x h
      exact (hx j hj.symm).elim
    · obtain ⟨j,hj⟩ := carry v hv
      exact ⟨j,hj.symm ▸ e⟩

#print axioms connected_domination_decomposition
end Graffiti133Camby
