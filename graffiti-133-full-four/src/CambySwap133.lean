import CambyPathEnds133

namespace Graffiti133Camby
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem tip_data {n : ℕ} (hn : 2≤n) {S : Finset V} {f : Fin n → V}
    (hf : InducedPath G f) (hin : Inside S f) {y z : V}
    (hy : PrivateAt G S (f ⟨0,by omega⟩) y) (hz : PrivateAt G S (f ⟨n-1,by omega⟩) z) :
    ∃ p : Fin (n+1) → V, InducedPath G p ∧ p ⟨0,by omega⟩=y ∧
      (∀ i, z≠p i) ∧ G.Adj z (p ⟨n,by omega⟩) ∧
      (∀ i : Fin (n+1), 0 < i.val → i.val < n → ¬G.Adj z (p i)) ∧
      (∀ i : Fin n, ∃ j, p j=f i) := by
  have offy (i : Fin n) : y≠f i := fun e => hy.1 (e.symm ▸ hin i)
  have offz (i : Fin n) : z≠f i := fun e => hz.1 (e.symm ▸ hin i)
  have ney (i : Fin n) (h : 0 < i.val) : ¬G.Adj y (f i) :=
    hy.2.2 _ (hin i) (hf.1.ne (fun e => (Nat.ne_of_gt h) (congrArg Fin.val e)))
  have neyZ : z≠y := by
    intro eq
    have ne : f (⟨0,by omega⟩ : Fin n) ≠ f ⟨n-1,by omega⟩ :=
      hf.1.ne (fun e => by have h := congrArg Fin.val e; change 0=n-1 at h; omega)
    exact hz.2.2 _ (hin _) ne (eq.symm ▸ hy.2.1)
  obtain ⟨p,hp,h0,ht⟩ := prepend_induced_with_positions (by omega) hf y offy hy.2.1 ney
  refine ⟨p,hp,h0,?_,?_,?_,?_⟩
  · intro i
    by_cases h : i.val=0
    · have q : i=⟨0,by omega⟩ := Fin.ext h
      rw [q,h0]
      exact neyZ
    · rw [ht i (Nat.pos_of_ne_zero h)]
      exact offz _
  · have q := ht ⟨n,by omega⟩ (by change 0 < n; omega)
    exact q.symm ▸ hz.2.1
  · intro i hi h
    rw [ht i hi]
    apply hz.2.2 _ (hin _)
    apply hf.1.ne
    intro q
    have hh := congrArg Fin.val q
    change i.val-1 = n-1 at hh
    omega
  · intro i
    let j : Fin (n+1) := ⟨i.val+1,by have := i.isLt; omega⟩
    refine ⟨j,?_⟩
    rw [ht j (by change 0 < i.val+1; omega)]
    exact congrArg f (Fin.ext (by change i.val+1-1=i.val; omega))

theorem either_adjacent_private_or_more_path {n : ℕ} (hn : 2≤n) {S : Finset V} {f : Fin n → V}
    (hf : InducedPath G f) (hin : Inside S f) {y z : V}
    (hy : PrivateAt G S (f ⟨0,by omega⟩) y) (hz : PrivateAt G S (f ⟨n-1,by omega⟩) z)
    (no : NoPath G (n+2)) : G.Adj z y := by
  by_contra ne
  obtain ⟨p,hp,h0,off,adj,nt,_⟩ := tip_data hn hf hin hy hz
  apply no
  refine ⟨Fin.lastCases z p,append_induced (by omega) hp z off adj ?_⟩
  intro i hi
  by_cases h : i.val=0
  · have q : i=⟨0,by omega⟩ := Fin.ext h
    rw [q,h0]
    exact ne
  · exact nt i (Nat.pos_of_ne_zero h) (by omega)

theorem cycle_of_private_tips {n : ℕ} (hn : 2≤n) {S : Finset V} {f : Fin n → V}
    (hf : InducedPath G f) (hin : Inside S f) {y z : V}
    (hy : PrivateAt G S (f ⟨0,by omega⟩) y) (hz : PrivateAt G S (f ⟨n-1,by omega⟩) z)
    (no : NoPath G (n+2)) :
    ∃ H : Hole G (n+2), ∀ i, ∃ j, H.c j = f i := by
  have ed := either_adjacent_private_or_more_path hn hf hin hy hz no
  obtain ⟨p,hp,h0,off,adj,nt,contain⟩ := tip_data hn hf hin hy hz
  let c (i : Fin ((n+1)+1)) : V :=
    if hi : i.val < n+1 then p ⟨i.val,hi⟩ else z
  have cP (i : Fin (n+1)) : c i.castSucc = p i := by simp [c,i.isLt]
  have cZ : c (Fin.last (n+1)) = z := by simp [c]
  have near (i : Fin (n+1)) : G.Adj z (p i) ↔ i.val=0 ∨ i.val=n := by
    constructor
    · intro e
      by_cases a : i.val=0
      · exact Or.inl a
      · by_cases b : i.val=n
        · exact Or.inr b
        · exact (nt i (Nat.pos_of_ne_zero a) (by have:=i.isLt; omega) e).elim
    · rintro (h|h)
      · have eq : i=⟨0,by omega⟩ := Fin.ext h
        rw [eq,h0]
        exact ed
      · have eq : i=⟨n,by omega⟩ := Fin.ext h
        exact eq.symm ▸ adj
  have ringOld (i j : Fin (n+1)) :
      Cyclic i.castSucc j.castSucc ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    change (i.val+1=j.val ∨ j.val+1=i.val ∨
      (i.val=0 ∧ j.val+1=(n+1)+1) ∨ (j.val=0 ∧ i.val+1=(n+1)+1)) ↔ _
    have hi := i.isLt
    have hj := j.isLt
    omega
  have ringLast (i : Fin (n+1)) : Cyclic (Fin.last (n+1)) i.castSucc ↔ i.val=0 ∨ i.val=n := by
    change (n+1+1=i.val ∨ i.val+1=n+1 ∨
      (n+1=0 ∧ i.val+1=(n+1)+1) ∨ (i.val=0 ∧ (n+1)+1=(n+1)+1)) ↔ _
    have hi := i.isLt
    omega
  have inj : Function.Injective c := by
    intro i j
    refine Fin.lastCases ?_ (fun i=>?_) i <;> refine Fin.lastCases ?_ (fun j=>?_) j
    · intro _; rfl
    · rw [cP,cZ]; exact fun e => (off _ e).elim
    · rw [cP,cZ]; exact fun e => (off _ e.symm).elim
    · rw [cP,cP]; exact fun e => congrArg Fin.castSucc (hp.1 e)
  have hRel (i j : Fin ((n+1)+1)) : G.Adj (c i) (c j) ↔ Cyclic i j := by
    refine Fin.lastCases ?_ (fun i=>?_) i <;> refine Fin.lastCases ?_ (fun j=>?_) j
    · rw [cZ]
      refine iff_of_false (G.loopless _) ?_
      unfold Cyclic
      simp only [Fin.val_last]
      omega
    · rw [cZ,cP,near,ringLast]
    · rw [cP,cZ,G.adj_comm,near,(cyclic_symm _ _),ringLast]
    · rw [cP,cP,ringOld]
      rcases lt_trichotomy i j with h|rfl|h
      · rw [hp.2 _ _ h]
        change i.val < j.val at h
        exact ⟨Or.inl,fun q => q.resolve_right (by omega)⟩
      · simp [G.loopless]
      · rw [G.adj_comm,hp.2 _ _ h]
        change j.val < i.val at h
        exact ⟨Or.inr,fun q => q.resolve_left (by omega)⟩
  refine ⟨⟨c,inj,hRel⟩,?_⟩
  intro i
  obtain ⟨j,h⟩ := contain i
  exact ⟨j.castSucc,(cP j).trans h⟩

theorem swap_tip {n : ℕ} (hn : 2≤n) {S : Finset V} (hm : MinimalSize G S)
    {f : Fin n → V} (hf : InducedPath G f) (hin : Inside S f) {y : V}
    (hy : PrivateAt G S (f ⟨0,by omega⟩) y) (no : NoPath G (n+2)) :
    MinimalSize G (insert y (S.erase (f ⟨n-1,by omega⟩))) := by
  classical
  let a := f (⟨0,by omega⟩ : Fin n)
  let b := f (⟨n-1,by omega⟩ : Fin n)
  let T := insert y (S.erase b)
  have n1 : a≠b := hf.1.ne (fun e => by have q := congrArg Fin.val e; change 0=n-1 at q; omega)
  have noInner : NoPathIn G S (n+1) := no_shorter_inside (by omega) hm no
  have c : (G.induce (T : Set V)).Connected :=
    connected_insert_of_edge (noncut_last hn hm.1 hf hin noInner)
      (Finset.mem_erase.mpr ⟨n1,hin _⟩) hy.2.1
  have card : T.card = S.card := by
    rw [Finset.card_insert_of_not_mem (show y∉S.erase b from fun h => hy.1 (Finset.erase_subset _ _ h)),
      Finset.card_erase_add_one (hin (⟨n-1,by omega⟩ : Fin n))]
  refine ⟨⟨c,?_⟩,fun U h => card ▸ hm.2 U h⟩
  intro z
  by_contra fail
  have noMem : z∉T := fun h => fail (Or.inl h)
  have noEdge (w : V) (hw : w∈T) : ¬G.Adj z w := fun e => fail (Or.inr ⟨w,hw,e⟩)
  let j : Fin n := ⟨n-2,by omega⟩
  have e : G.Adj b (f j) := ((hf.2 j ⟨n-1,by omega⟩ (by change n-2 < n-1; omega)).mpr (by change n-2+1=n-1; omega)).symm
  have znb : z≠b := fun eq => noEdge (f j)
    (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e.ne.symm,hin j⟩)) (eq.symm ▸ e)
  have out : z∉S := fun h => noMem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨znb,h⟩))
  obtain hz | ⟨w,hw,ew⟩ := hm.1.2 z
  · exact out hz
  have wb : w=b := by
    by_contra wn
    exact noEdge w (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨wn,hw⟩)) ew
  have priv : PrivateAt G S b z :=
    ⟨out,wb ▸ ew,fun w hw ne => noEdge w (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ne,hw⟩))⟩
  exact noEdge y (Finset.mem_insert_self _ _) (either_adjacent_private_or_more_path hn hf hin hy priv no)

#print axioms swap_tip
#print axioms cycle_of_private_tips
end Graffiti133Camby
