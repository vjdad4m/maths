import FiniteLayout
import EmbedPlacement

open private pred_mem succ_mem from CompactOmission
open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

def SparseMust {n : ℕ} (b : Layout n) (skipped : List ℕ) (i j : Fin (n+1)) : Prop :=
  (i.val+1 = j.val ∧ j.val < n ∧ i.val ∉ skipped) ∨ (i = Fin.last n ∧ j ∈ b.ports)

instance sparseMustDecidable {n : ℕ} (b : Layout n) (skipped : List ℕ) (i j : Fin (n+1)) :
    Decidable (SparseMust b skipped i j) := by unfold SparseMust; infer_instance

def SparseConsistent {n : ℕ} (b : Layout n) (skipped : List ℕ) (m : Fin 3) (d : Family n) : Prop :=
  ∀ i j, d.pattern.slot i j = none →
    if d.pattern.fixed i j then SparseMust b skipped i j ∨ SparseMust b skipped j i
    else Off b m i j ∨ Off b m j i

instance sparseConsistentDecidable {n : ℕ} (b : Layout n) (skipped : List ℕ) (m : Fin 3) (d : Family n) :
    Decidable (SparseConsistent b skipped m d) := by unfold SparseConsistent; infer_instance

variable {V : Type*} {G : SimpleGraph V}

theorem sparse_row [DecidableRel G.Adj] {n : ℕ} {b : Layout n} {m : Fin 3}
    {f : Fin (n+1) ↪ V} {d : Family n} {skipped : List ℕ}
    (h : SparseConsistent b skipped m d)
    (real : ∀ i j, SparseMust b skipped i j → G.Adj (f i) (f j))
    (off : ∀ i j, Off b m i j → ¬ G.Adj (f i) (f j)) :
    ∃ row, ∀ i j, G.Adj (f i) (f j) ↔ d.pattern.edge row i j = true := by
  letI : BEq (Fin (n+1) × Fin (n+1)) := instBEqOfDecidableEq
  let flags := fun k : Fin d.choices.length =>
    decide (G.Adj (f (d.choices.get k).1) (f (d.choices.get k).2))
  refine ⟨encode flags,?_⟩
  intro i j
  by_cases hc : (min i j,max i j) ∈ d.choices
  · let k : Fin d.choices.length := ⟨_,List.idxOf_lt_length hc⟩
    have key : d.choices.get k = (min i j,max i j) := by
      exact List.getElem_idxOf (List.idxOf_lt_length hc)
    have same : d.pattern.slot i j = some k.val := by
      simp only [Family.pattern,k,dif_pos k.isLt,if_pos k.isLt]
    simp only [Pattern.edge,same,encode_bit flags k]
    change G.Adj (f i) (f j) ↔ decide (G.Adj (f (d.choices.get k).1) (f (d.choices.get k).2)) = true
    rw [key,decide_eq_true_eq]
    rcases le_total i j with hi|hj
    · rw [min_eq_left hi,max_eq_right hi]
    · rw [min_eq_right hj,max_eq_left hj,G.adj_comm]
  · have none : d.pattern.slot i j = none := by simp [Family.pattern,List.idxOf_eq_length hc]
    rw [Pattern.edge,none]
    have rule := h i j none
    cases e : d.pattern.fixed i j with
    | false =>
      simp only [e,Bool.false_eq_true,if_false] at rule
      exact iff_of_false (rule.elim (off _ _) (fun eq adj => off _ _ eq adj.symm)) Bool.false_ne_true
    | true =>
      simp only [e,if_true] at rule
      exact iff_of_true (rule.elim (real _ _) (fun eq => (real _ _ eq).symm)) rfl

theorem path_subchain {S : Set V} (p : PathOn G S) {L B R : List V}
    (split : p.vertices = L ++ B ++ R) : B.Chain' G.Adj :=
  (split ▸ p.chain).left_of_append.right_of_append

theorem adjacent_on_path {S : Set V} (p : PathOn G S) {L R : List V} {x y : V}
    (split : p.vertices = L ++ x :: y :: R) : G.Adj x y :=
  (split ▸ p.chain).right_of_append.rel_head

variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- The nonedge constraints use only the two immediate contacts of
each port. They apply through arbitrarily long gaps. -/
theorem sparse_off {n : ℕ} (b : Layout n) (m : Fin 3) {f : Fin (n+1) ↪ V}
    (p : PathOn G {v | v ≠ f (Fin.last n)}) (noTrace : ¬ Catalogue.Traceable G)
    (around : ∀ i, ∃ L R : List V, p.vertices = L ++ f (b.prev i) :: f (b.port i) :: f (b.next i) :: R)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (b.port i)) (f (b.port j)))
    (dz : G.degree (f (Fin.last n)) = 3) (dm : G.degree (f (b.port m)) = 3) :
    ∀ i j, Off b m i j → ¬ G.Adj (f i) (f j) := by
  have ls (i : Fin 3) : f (b.prev i) ∈ p.predecessors := by
    obtain ⟨A,C,s⟩ := around i
    exact pred_mem (R := f (b.next i) :: C) s (za i)
  have rs (i : Fin 3) : f (b.next i) ∈ p.rev.predecessors := by
    obtain ⟨A,C,s⟩ := around i
    exact succ_mem (L := A ++ [f (b.prev i)])
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using s) (za i)
  have onlyZ (i : Fin (n+1)) (h : G.Adj (f (Fin.last n)) (f i)) : i ∈ b.ports := by
    obtain ⟨v,hv,eq⟩ := three_names_exhaust_neighbors f
      (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 1))
      (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 2))
      (b.port.injective.ne (by decide : (1 : Fin 3) ≠ 2)) dz (za 0) (za 1) (za 2) _ h
    exact f.injective eq ▸ (show v ∈ b.ports from hv)
  have onlyMate (i : Fin (n+1)) (h : G.Adj (f (b.port m)) (f i)) : i ∈ b.mateContacts m := by
    have hl : (Fin.last n : Fin (n+1)) ≠ b.prev m := by
      intro eq
      have u := congrArg Fin.val eq
      change n = (b.port m).val - 1 at u
      have v := b.interior m
      omega
    have hr : (Fin.last n : Fin (n+1)) ≠ b.next m := by
      intro eq
      have u := congrArg Fin.val eq
      change n = (b.port m).val + 1 at u
      have v := b.interior m
      omega
    have hlr : b.prev m ≠ b.next m := by
      intro eq
      have u := congrArg Fin.val eq
      change (b.port m).val - 1 = (b.port m).val + 1 at u
      omega
    obtain ⟨A,C,s⟩ := around m
    have left := adjacent_on_path p s
    have right : G.Adj (f (b.port m)) (f (b.next m)) := adjacent_on_path p
      (L := A ++ [f (b.prev m)]) (R := C)
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using s)
    obtain ⟨j,hj,eq⟩ := three_names_exhaust_neighbors f hl hr hlr dm (za m).symm left.symm right _ h
    exact f.injective eq ▸ hj
  intro i j rule
  rcases rule with rfl|⟨iP,jP⟩|⟨iP,jP⟩|⟨iP,jP⟩|⟨rfl,nP⟩|⟨rfl,nP⟩
  · exact G.loopless _
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp iP
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp jP
    exact ind a c
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp iP
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp jP
    exact p.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem (ls a)) _
      (Finset.mem_insert_of_mem (ls c))
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp iP
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp jP
    exact p.rev.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem (rs a)) _
      (Finset.mem_insert_of_mem (rs c))
  · exact fun h => nP (onlyZ _ h)
  · exact fun h => nP (onlyMate _ h)

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem embed_ordinary_sublist {z : V} (p : PathOn G {x | x ≠ z}) (S : List V)
    (sub : S.Sublist p.vertices) :
    ∃ f : Fin (S.length+1) ↪ V, f (Fin.last S.length) = z ∧ block f = S := by
  have nd : S.Nodup := sub.nodup p.nodup
  have off : z ∉ S := fun h => (p.covers z).mp (sub.subset h) rfl
  have full : (S ++ [z]).Nodup :=
    List.nodup_append.mpr ⟨nd,by simp,by simpa using off⟩
  let f : Fin (S.length+1) ↪ V :=
    ⟨fun i => (S ++ [z]).get (i.cast (by simp)),by
      intro i j e
      have eq := List.nodup_iff_injective_get.mp full e
      exact Fin.ext (congrArg (fun u : Fin (S ++ [z]).length => u.val) eq)⟩
  refine ⟨f,?_,?_⟩
  · change (S ++ [z])[S.length]'(by simp) = z
    simp
  · refine List.ext_getElem (block_length f) ?_
    intro i il ir
    let t : Fin (S.length+1) := ⟨i,by omega⟩
    rw [block_get f t ir]
    change (S ++ [z])[i]'(by simp; omega) = S[i]
    rw [List.getElem_append_left ir]

end Graffiti199Depleted.WiderOmission
