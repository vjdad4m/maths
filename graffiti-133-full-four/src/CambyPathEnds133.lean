import CambyDomBase133

namespace Graffiti133Camby
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem reverse_path {n : ℕ} {f : Fin n → V} (hf : InducedPath G f) :
    InducedPath G (f ∘ Fin.rev) := by
  refine ⟨hf.1.comp Fin.rev_involutive.injective,?_⟩
  intro i j h
  have ht : Fin.rev j < Fin.rev i := by
    change i.val < j.val at h
    simp only [Fin.lt_def,Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    omega
  change G.Adj (f (Fin.rev i)) (f (Fin.rev j)) ↔ _
  rw [G.adj_comm,hf.2 _ _ ht]
  simp only [Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem no_shorter_inside {n : ℕ} (hn : 2 ≤ n) {S : Finset V}
    (hS : MinimalSize G S) (hNo : NoPath G (n+1)) :
    NoPathIn G S n := by
  rintro ⟨f,hf,hin⟩
  let i₀ : Fin n := ⟨0,by omega⟩
  let i₁ : Fin n := ⟨1,by omega⟩
  have ne : f i₁ ≠ f i₀ := hf.1.ne (by intro e; have hh := congrArg Fin.val e; simp [i₀,i₁] at hh)
  have e : G.Adj (f i₀) (f i₁) := (hf.2 _ _ (by change 0 < 1; decide)).mpr rfl
  by_cases conn : (G.induce (↑(S.erase (f i₀)) : Set V)).Connected
  · obtain ⟨z,off,ez,nz⟩ := private_of_noncut hS (hin i₀)
      (Finset.mem_erase.mpr ⟨ne,hin i₁⟩) e conn
    have fresh (i : Fin n) : z≠f i := fun eq => off (eq.symm ▸ hin i)
    have no (i : Fin n) (hi : 0 < i.val) : ¬G.Adj z (f i) :=
      nz _ (hin _) (hf.1.ne (fun eq => (Nat.ne_of_gt hi) (congrArg Fin.val eq)))
    obtain ⟨p,hp,_,_⟩ := prepend_induced_with_positions (by omega) hf z fresh ez no
    exact hNo ⟨p,hp⟩
  · obtain ⟨z,_,off,ez,nz⟩ := cut_tip_witness hn hf hin hS.1.1 conn
    obtain ⟨p,hp,_,_⟩ := prepend_induced_with_positions (by omega) hf z off ez nz
    exact hNo ⟨p,hp⟩

theorem noncut_first {n : ℕ} (hn : 2 ≤ n) {S : Finset V} {f : Fin n → V}
    (hS : CD G S) (hf : InducedPath G f) (hin : Inside S f)
    (no : NoPathIn G S (n+1)) :
    (G.induce (↑(S.erase (f ⟨0,by omega⟩)) : Set V)).Connected := by
  apply Classical.byContradiction
  intro fail
  obtain ⟨z,hz,off,ez,nt⟩ := cut_tip_witness hn hf hin hS.1 fail
  obtain ⟨p,hp,hhead,htail⟩ := prepend_induced_with_positions (by omega) hf z off ez nt
  apply no ⟨p,hp,?_⟩
  intro i
  by_cases h : i.val=0
  · have eq : i=⟨0,by omega⟩ := Fin.ext h
    rw [eq,hhead]
    exact hz
  · rw [htail i (Nat.pos_of_ne_zero h)]
    exact hin _

theorem noncut_last {n : ℕ} (hn : 2 ≤ n) {S : Finset V} {f : Fin n → V}
    (hS : CD G S) (hf : InducedPath G f) (hin : Inside S f)
    (no : NoPathIn G S (n+1)) :
    (G.induce (↑(S.erase (f ⟨n-1,by omega⟩)) : Set V)).Connected := by
  have h := noncut_first hn hS (reverse_path hf) (fun i => hin (Fin.rev i)) no
  exact h

theorem private_first {n : ℕ} (hn : 2 ≤ n) {S : Finset V} {f : Fin n → V}
    (hS : MinimalSize G S) (hf : InducedPath G f) (hin : Inside S f)
    (no : NoPathIn G S (n+1)) : ∃ y, PrivateAt G S (f ⟨0,by omega⟩) y := by
  let i₀ : Fin n := ⟨0,by omega⟩
  let i₁ : Fin n := ⟨1,by omega⟩
  have ne : f i₁ ≠ f i₀ := hf.1.ne (by intro h; have q := congrArg Fin.val h; simp [i₀,i₁] at q)
  exact private_of_noncut hS (hin i₀) (Finset.mem_erase.mpr ⟨ne,hin i₁⟩)
    ((hf.2 _ _ (by change 0 < 1; decide)).mpr rfl) (noncut_first hn hS.1 hf hin no)

theorem private_last {n : ℕ} (hn : 2 ≤ n) {S : Finset V} {f : Fin n → V}
    (hS : MinimalSize G S) (hf : InducedPath G f) (hin : Inside S f)
    (no : NoPathIn G S (n+1)) : ∃ y, PrivateAt G S (f ⟨n-1,by omega⟩) y := by
  exact private_first hn hS (reverse_path hf) (fun i => hin (Fin.rev i)) no

theorem append_induced {n : ℕ} (hn : 0 < n) {f : Fin n → V} (hf : InducedPath G f)
    (z : V) (off : ∀ i,z≠f i) (adj : G.Adj z (f ⟨n-1,by omega⟩))
    (none : ∀ i : Fin n, i.val+1 < n → ¬G.Adj z (f i)) :
    InducedPath G (Fin.lastCases z f) := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro e; exact (off _ (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using e)).elim
    · intro e; exact (off _ (by simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using e.symm)).elim
    · intro e
      exact congrArg Fin.castSucc (hf.1 (by simpa only [Fin.lastCases_castSucc] using e))
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; exact (lt_irrefl _ h).elim
    · intro h
      have q := Fin.castSucc_lt_last j
      exact ((lt_asymm q) h).elim
    · intro _
      simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
      change G.Adj (f i) z ↔ i.val+1=n
      by_cases h : i.val+1=n
      · have eq : i=⟨n-1,by omega⟩ := Fin.ext (by change i.val=n-1; omega)
        exact ⟨fun _ => h,fun _ => eq.symm ▸ adj.symm⟩
      · exact iff_of_false (fun e => none i (by have := i.isLt; omega) e.symm) h
    · intro h
      simpa only [Fin.lastCases_castSucc] using hf.2 i j h

theorem connected_insert_of_edge {S : Finset V} (h : (G.induce (S:Set V)).Connected)
    {a b : V} (ha : a∈S) (e : G.Adj b a) :
    (G.induce (↑(insert b S):Set V)).Connected := by
  classical
  rw [connected_iff_exists_forall_reachable]
  let sub : (S : Set V) ≤ (↑(insert b S):Set V) := fun _ x => Finset.mem_insert_of_mem x
  let emb := (G.induceHomOfLE sub).toHom
  refine ⟨emb ⟨a,ha⟩,?_⟩
  intro v
  rcases Finset.mem_insert.mp v.property with hit | hit
  · have ee : (G.induce (↑(insert b S):Set V)).Adj (emb ⟨a,ha⟩) v := by
      change G.Adj a v.val
      rw [hit]
      exact e.symm
    exact ⟨Walk.cons ee Walk.nil⟩
  · obtain ⟨p⟩ := h ⟨a,ha⟩ ⟨v.val,hit⟩
    exact ⟨p.map emb⟩

#print axioms no_shorter_inside
#print axioms noncut_last
#print axioms append_induced
end Graffiti133Camby
