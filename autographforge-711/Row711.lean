import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! One more allowed white neighbor saves one initial vertex, up to minimum degree. -/
namespace ForcingDrop711
open Finset Function SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/- These definitions follow the published BalancedForcing module. -/
def step (k : ℕ) (S : Finset V) : Finset V :=
  S ∪ univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, G.Adj v w ∧ (G.neighborFinset v \ S).card ≤ k)

def full (k : ℕ) (S : Finset V) : Prop := (step G k)^[Fintype.card V] S = univ

noncomputable def forcing (k : ℕ) : ℕ :=
  sInf {r | ∃ S : Finset V, S.card = r ∧ full G k S}

private theorem persistent (k : ℕ) (S : Finset V) : S ⊆ step G k S :=
  subset_union_left

private theorem mem_step {S : Finset V} {k : ℕ} {w : V} :
    w ∈ step G k S ↔ w ∈ S ∨ ∃ v ∈ S, G.Adj v w ∧ (G.neighborFinset v \ S).card ≤ k := by
  simp only [step, mem_union, mem_filter, mem_univ, true_and]
  by_cases h : w ∈ S <;> simp [h]

private theorem step_mono {k l : ℕ} {S T : Finset V} (h : k ≤ l) (sub : S ⊆ T) :
    step G k S ⊆ step G l T := by
  intro w hw
  rw [mem_step] at hw ⊢
  rcases hw with hs | ⟨v,hv,adj,cap⟩
  · exact Or.inl (sub hs)
  · exact Or.inr ⟨v,sub hv,adj,
      (card_le_card (sdiff_subset_sdiff (Subset.rfl) sub)).trans (cap.trans h)⟩

private theorem iterate_mono {k l : ℕ} {S T : Finset V} (h : k ≤ l) (sub : S ⊆ T) (i : ℕ) :
    (step G k)^[i] S ⊆ (step G l)^[i] T := by
  induction i with
  | zero => exact sub
  | succ i ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact step_mono G h ih

private theorem step_univ (k : ℕ) : step G k univ = univ :=
  eq_univ_of_forall (fun v => persistent G k univ (mem_univ v))

/-- By round n the process has stabilized, since each changing round adds a vertex. -/
theorem stable (k : ℕ) (S : Finset V) :
    step G k ((step G k)^[Fintype.card V] S) = (step G k)^[Fintype.card V] S := by
  let A := fun i : ℕ => (step G k)^[i] S
  have next (i : ℕ) : A (i+1) = step G k (A i) := iterate_succ_apply' ..
  have progress (i : ℕ) : step G k (A i) = A i ∨ i ≤ (A i).card := by
    induction i with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ i ih =>
      rcases ih with fixed | size
      · exact Or.inl (by rw [next, fixed, fixed])
      · by_cases fixed : step G k (A i) = A i
        · exact Or.inl (by rw [next, fixed, fixed])
        · have strict := card_lt_card (ssubset_of_subset_of_ne (persistent G k (A i)) (Ne.symm fixed))
          exact Or.inr (by rw [next]; omega)
  rcases progress (Fintype.card V) with fixed | size
  · exact fixed
  · have allVerts : A (Fintype.card V) = univ :=
      eq_of_subset_of_card_le (subset_univ _) (by simpa using size)
    change step G k (A _) = A _
    rw [allVerts, step_univ]

private theorem full_univ (k : ℕ) : full G k univ :=
  iterate_fixed (step_univ G k) _

private theorem attained (k : ℕ) : ∃ S : Finset V, S.card = forcing G k ∧ full G k S :=
  Nat.sInf_mem (s := {r | ∃ S : Finset V, S.card = r ∧ full G k S})
    ⟨_,univ,rfl,full_univ G k⟩

private theorem forcing_le {k : ℕ} {S : Finset V} (h : full G k S) : forcing G k ≤ S.card :=
  Nat.sInf_le (s := {r | ∃ T : Finset V, T.card = r ∧ full G k T}) ⟨S,rfl,h⟩

/-- A successful seed contains a vertex with at most k white neighbors.
This includes an already fully colored seed, when every white count is zero. -/
private theorem first_vertex [Nonempty V] {k : ℕ} {S : Finset V} (h : full G k S) :
    ∃ v ∈ S, (G.neighborFinset v \ S).card ≤ k := by
  by_contra none
  have fixed : step G k S = S := by
    apply Subset.antisymm _ (persistent G k S)
    intro w hw
    rcases (mem_step G).mp hw with hs | ⟨v,hv,_,cap⟩
    · exact hs
    · exact (none ⟨v,hv,cap⟩).elim
  change (step G k)^[Fintype.card V] S = univ at h
  rw [iterate_fixed fixed] at h
  subst S
  let v := Classical.choice ‹Nonempty V›
  have empty : G.neighborFinset v \ univ = ∅ := sdiff_eq_empty_iff_subset.mpr (subset_univ _)
  exact none ⟨v,mem_univ v,by rw [empty,card_empty]; exact Nat.zero_le _⟩

/-- GraphCalc starts its search for a zero-forcing set at minimum degree.
This lower bound verifies that it cannot skip a feasible cardinality. -/
theorem search_start [Nonempty V] {S : Finset V} (h : full G 1 S) :
    G.minDegree ≤ S.card := by
  obtain ⟨v,hv,cap⟩ := first_vertex G h
  let N := G.neighborFinset v
  have no : v ∉ N ∩ S := fun hv' => G.loopless v
    ((G.mem_neighborFinset _ _).mp (mem_inter.mp hv').1)
  have sub : insert v (N ∩ S) ⊆ S := insert_subset hv inter_subset_right
  have size := card_le_card sub
  rw [card_insert_of_not_mem no] at size
  have eq := card_sdiff_add_card_inter N S
  change (N \ S).card ≤ 1 at cap
  have deg : G.degree v = N.card := (G.card_neighborFinset_eq_degree v).symm
  have lower := G.minDegree_le_degree v
  omega

/-- Pairwise disjoint closed neighborhoods let several initially eligible vertices
each save t seeds in the *same* round at the same relaxed threshold. Only their
local degrees matter. -/
theorem packed_seed_savings {k t : ℕ} {S C : Finset V} (h : full G k S)
    (centers : C ⊆ S)
    (eligible : ∀ v ∈ C, (G.neighborFinset v \ S).card ≤ k)
    (degree : ∀ v ∈ C, k+t ≤ G.degree v)
    (apart : C.toSet.PairwiseDisjoint (fun v => insert v (G.neighborFinset v))) :
    ∃ B ⊆ S, B.card + C.card*t = S.card ∧ full G (k+t) B := by
  classical
  let N := G.neighborFinset
  have chooseAt (v : V) (hv : v ∈ C) : ∃ T ⊆ N v ∩ S, T.card = t := by
    have eq := card_sdiff_add_card_inter (N v) S
    have deg : k+t ≤ (N v).card := by simpa [N] using degree v hv
    have cap : ((N v) \ S).card ≤ k := eligible v hv
    exact exists_subset_card_eq (by omega)
  let parts (v : V) := if hv : v ∈ C then (chooseAt v hv).choose else ∅
  have spec {v : V} (hv : v ∈ C) : parts v ⊆ N v ∩ S ∧ (parts v).card = t := by
    simpa only [parts,dif_pos hv] using (chooseAt v hv).choose_spec
  have inside {v : V} (hv : v ∈ C) :
      parts v ⊆ insert v (N v) :=
    (spec hv).1.trans (inter_subset_left.trans (subset_insert _ _))
  let removed := C.biUnion parts
  have disj : C.toSet.PairwiseDisjoint parts := by
    intro v hv u hu diff
    exact (apart hv hu diff).mono (inside hv) (inside hu)
  have size : removed.card = C.card*t := by
    change (C.biUnion parts).card = C.card*t
    rw [card_biUnion disj]
    calc ∑ v ∈ C, (parts v).card = ∑ _v ∈ C, t := sum_congr rfl (fun _ hv => (spec hv).2)
         _ = _ := by simp
  have rem_sub : removed ⊆ S := by
    intro w hw
    obtain ⟨v,hv,hwv⟩ := mem_biUnion.mp hw
    exact (mem_inter.mp ((spec hv).1 hwv)).2
  let B := S \ removed
  have localize {v w : V} (hv : v ∈ C) (hw : w ∈ insert v (N v)) (hr : w ∈ removed) :
      w ∈ parts v := by
    obtain ⟨u,hu,hwu⟩ := mem_biUnion.mp hr
    by_cases eq : v = u
    · exact eq ▸ hwu
    · exact (disjoint_left.mp (apart hv hu eq) hw (inside hu hwu)).elim
  have recover : S ⊆ step G (k+t) B := by
    intro w hw
    apply (mem_step G).mpr
    by_cases hr : w ∈ removed
    · obtain ⟨v,hv,hwp⟩ := mem_biUnion.mp hr
      have keep : v ∉ removed := by
        intro hr'
        have hself := (mem_inter.mp ((spec hv).1 (localize hv (mem_insert_self ..) hr'))).1
        exact G.loopless v ((G.mem_neighborFinset _ _).mp hself)
      have whites : N v \ B ⊆ (N v \ S) ∪ parts v := by
        intro x hx
        obtain ⟨hn,hnb⟩ := mem_sdiff.mp hx
        by_cases hs : x ∈ S
        · by_cases hr' : x ∈ removed
          · exact mem_union_right _ (localize hv (mem_insert_of_mem hn) hr')
          · exact (hnb (mem_sdiff.mpr ⟨hs,hr'⟩)).elim
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hn,hs⟩)
      have cap := eligible v hv
      have room : (N v \ B).card ≤ k+t :=
        (card_le_card whites).trans ((card_union_le _ _).trans (by
          rw [(spec hv).2]; exact Nat.add_le_add_right cap t))
      exact Or.inr ⟨v,mem_sdiff.mpr ⟨centers hv,keep⟩,
        (G.mem_neighborFinset _ _).mp (mem_inter.mp ((spec hv).1 hwp)).1,room⟩
    · exact Or.inl (mem_sdiff.mpr ⟨hw,hr⟩)
  refine ⟨B,sdiff_subset,by simpa [B,size] using card_sdiff_add_card_eq_card rem_sub,?_⟩
  have replay := iterate_mono G (Nat.le_add_right k t) recover (Fintype.card V)
  change (step G k)^[Fintype.card V] S = univ at h
  rw [h, ← iterate_succ_apply, iterate_succ_apply', stable] at replay
  exact Subset.antisymm (subset_univ _) replay

/-- A successful seed has at least one eligible center. -/
theorem seed_savings [Nonempty V] {k t : ℕ} {S : Finset V} (h : full G k S)
    (degree : ∀ v, k+t ≤ G.degree v) :
    ∃ B ⊆ S, B.card + t = S.card ∧ full G (k+t) B := by
  obtain ⟨v,hv,cap⟩ := first_vertex G h
  have one := packed_seed_savings G (C := {v}) h (singleton_subset_iff.mpr hv)
    (by simpa using cap) (fun u _ => degree u) (by simp)
  simpa using one

theorem forcing_drop [Nonempty V] (k t : ℕ) (degree : ∀ v, k+t ≤ G.degree v) :
    forcing G (k+t) + t ≤ forcing G k := by
  obtain ⟨S,sz,h⟩ := attained G k
  obtain ⟨B,_,szB,hB⟩ := seed_savings G h degree
  have bound := forcing_le G hB
  omega

/-- The signed integer form of normalized physical row 711. -/
theorem row711 (order : 2 ≤ Fintype.card V) (conn : G.Connected)
    (even : ∀ v, Even (G.degree v)) :
    (forcing G 2 : ℤ) ≤ (forcing G 1 : ℤ) + (-1) := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp order
  have lower (v : V) : 1+1 ≤ G.degree v := by
    have pos : 0 < G.degree v := by
      apply (G.degree_pos_iff_exists_adj v).mpr
      obtain ⟨w,diff⟩ := exists_ne v
      obtain ⟨walk⟩ := conn.preconnected v w
      cases walk with
      | nil => exact (diff rfl).elim
      | cons e _ => exact ⟨_,e⟩
    obtain ⟨a,ha⟩ := even v
    omega
  have bound := forcing_drop G 1 1 lower
  change forcing G 2 + 1 ≤ forcing G 1 at bound
  omega


local instance completeDecidable (U : Type*) [DecidableEq U] : DecidableRel (completeGraph U).Adj :=
  fun v w => inferInstanceAs (Decidable (v ≠ w))

local notation "K" => completeGraph V

/-- The exact complete-graph formula shows the savings are sharp at every
threshold. The maximum with one covers the single-vertex boundary as well. -/
theorem complete_forcing [Nonempty V] (k : ℕ) :
    forcing (completeGraph V) k = max 1 (Fintype.card V - k) := by
  have npos := Fintype.card_pos (α := V)
  have whites {S : Finset V} {v : V} (hv : v ∈ S) :
      (completeGraph V).neighborFinset v \ S = univ \ S := by
    ext w
    simp only [mem_sdiff, mem_neighborFinset, mem_univ, true_and]
    constructor
    · exact And.right
    · exact fun hw => ⟨fun e => hw (e ▸ hv),hw⟩
  apply le_antisymm
  · obtain ⟨S,_,size⟩ := exists_subset_card_eq (s := (univ : Finset V))
        (n := max 1 (Fintype.card V - k)) (by rw [card_univ]; omega)
    have pos : 0 < S.card := by omega
    obtain ⟨v,hv⟩ := card_pos.mp pos
    have once : step K k S = univ := by
      apply eq_univ_of_forall
      intro w
      by_cases hw : w ∈ S
      · exact persistent K k S hw
      · apply (mem_step K).mpr
        refine Or.inr ⟨v,hv,fun e => hw (e ▸ hv),?_⟩
        rw [whites hv,card_sdiff (subset_univ S),card_univ,size]
        omega
    have hfull : full K k S := by
      unfold full
      obtain ⟨i,eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt npos)
      rw [eq,iterate_succ_apply,once,iterate_fixed (step_univ K k)]
    exact (forcing_le K hfull).trans_eq size
  · obtain ⟨S,size,h⟩ := attained K k
    obtain ⟨v,hv,cap⟩ := first_vertex K h
    rw [whites hv,card_sdiff (subset_univ S),card_univ] at cap
    have pos := card_pos.mpr (show S.Nonempty from ⟨v,hv⟩)
    change max 1 (Fintype.card V - k) ≤ forcing K k
    omega

theorem complete_sharp [Nonempty V] (k t : ℕ) (h : k+t < Fintype.card V) :
    forcing (completeGraph V) (k+t) + t = forcing (completeGraph V) k := by
  rw [complete_forcing,complete_forcing]
  omega

/-- A sharp witness inside the exact row class. -/
theorem triangle_sharp :
    let H := completeGraph (Fin 3)
    2 ≤ Fintype.card (Fin 3) ∧ H.Connected ∧ (∀ v, Even (H.degree v)) ∧
      forcing H 2 = 1 ∧ forcing H 1 = 2 := by
  dsimp only
  refine ⟨by decide, by rw [completeGraph_eq_top]; exact top_connected, ?_, ?_⟩
  · intro v
    exact ⟨1, by decide +revert⟩
  · rw [complete_forcing,complete_forcing]
    decide

/-- Physical row 6318 omits the nontriviality hypothesis. Its antecedent
and the Eulerian property are simultaneously true on one vertex. -/
theorem singleton_boundary :
    let H := completeGraph (Fin 1)
    H.Connected ∧ (∀ v, Even (H.degree v)) ∧ forcing H 2 = forcing H 1 := by
  dsimp only
  refine ⟨by rw [completeGraph_eq_top]; exact top_connected, ?_, ?_⟩
  · intro v
    exact ⟨0, by decide +revert⟩
  · rw [complete_forcing, complete_forcing]
    decide

#print axioms triangle_sharp
#print axioms singleton_boundary
#print axioms complete_forcing
#print axioms complete_sharp
#print axioms search_start
#print axioms packed_seed_savings
#print axioms seed_savings
#print axioms forcing_drop
#print axioms row711
end ForcingDrop711
