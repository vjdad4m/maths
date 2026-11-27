import RemoteVacancyRails
import Mathlib.Data.List.Chain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteGapRunPacking
open SquareCap (FactorOn)
open RemoteVacancyRails (tile_path factor_disjUnion factor_single)
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem run_factor (P : List V) (nod : P.Nodup) (chain : P.Chain' G.Adj)
    (div : 3∣P.length) : FactorOn G P.toFinset := by
  match P with
  | [] =>
    exact ⟨∅,by simp,by simp,by simp⟩
  | [a] =>
    obtain ⟨n,h⟩:=div
    simp only [List.length_cons,List.length_nil] at h
    omega
  | [a,b] =>
    obtain ⟨n,h⟩:=div
    simp only [List.length_cons,List.length_nil] at h
    omega
  | a::b::c::tail =>
    have ab : G.Adj a b := (List.chain'_cons.mp chain).1
    have bc : G.Adj b c := (List.chain'_cons.mp (List.chain'_cons.mp chain).2).1
    have aNot := (List.nodup_cons.mp nod).1
    have bNot := (List.nodup_cons.mp (List.nodup_cons.mp nod).2).1
    have cNot := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp nod).2).2).1
    have ne : a≠c := fun e=>aNot (e.symm ▸ (by simp : c∈b::c::tail))
    have out : FactorOn G ({a,b,c}:Finset V) := factor_single (tile_path G ab bc ne)
    have rem : 3∣tail.length := by
      obtain ⟨n,h⟩ := div
      simp only [List.length_cons] at h
      exact ⟨n-1,by omega⟩
    have t := run_factor tail nod.tail.tail.tail chain.tail.tail.tail rem
    have apart : Disjoint ({a,b,c}:Finset V) tail.toFinset := by
      apply disjoint_left.mpr
      intro x xm xt
      have xt' := List.mem_toFinset.mp xt
      simp only [mem_insert,mem_singleton] at xm
      rcases xm with rfl|rfl|rfl
      · exact aNot (by simp [xt'])
      · exact bNot (by simp [xt'])
      · exact cNot xt'
    have j := factor_disjUnion out t apart
    have eq : ((a::b::c::tail):List V).toFinset=({a,b,c}:Finset V)∪tail.toFinset := by
      ext x
      simp [or_assoc]
    rwa [←eq] at j
termination_by P.length

/-- The input to this criterion is only a cover by disjoint ordered
runs of lengths divisible by three, not a smaller factor oracle. -/
def RunCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ B : Finset (List V),
    (∀ l∈B,l.Nodup ∧ l.Chain' G.Adj ∧ 3∣l.length) ∧
    (∀ l∈B,∀ k∈B,l≠k→Disjoint l.toFinset k.toFinset) ∧
    B.biUnion List.toFinset=S

theorem biUnion_factor {I : Type*} [DecidableEq I] (B : Finset I)
    (supp : I→Finset V) (tiles : ∀ i∈B,FactorOn G (supp i))
    (apart : ∀ i∈B,∀ j∈B,i≠j→Disjoint (supp i) (supp j)) :
    FactorOn G (B.biUnion supp) := by
  induction B using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp,by simp⟩
  | insert i B no ih =>
    have old := ih (fun j jm=>tiles j (mem_insert_of_mem jm))
      (fun j jm k km ne=>apart j (mem_insert_of_mem jm) k (mem_insert_of_mem km) ne)
    have x := tiles i (mem_insert_self _ _)
    have d : Disjoint (supp i) (B.biUnion supp) := by
      apply disjoint_left.mpr
      intro a ai aq
      obtain ⟨j,jm,aj⟩:=mem_biUnion.mp aq
      exact disjoint_left.mp (apart i (mem_insert_self _ _) j (mem_insert_of_mem jm)
        (fun e=>no (e.symm ▸ jm))) ai aj
    rw [biUnion_insert]
    exact factor_disjUnion x old d

theorem runCover_factor {S : Finset V} (h : RunCover G S) : FactorOn G S := by
  obtain ⟨runs,legal,apart,cover⟩ := h
  rw [←cover]
  exact biUnion_factor runs List.toFinset
    (fun l m=>run_factor l (legal l m).1 (legal l m).2.1 (legal l m).2.2) apart

/-- Returning the old endpoint q to the residual concatenates the two
intervals on its sides, including empty intervals. -/
theorem joined_at_factor (L R : List V) (q : V)
    (ln : L.Nodup) (rn : R.Nodup)
    (lc : L.Chain' G.Adj) (rc : R.Chain' G.Adj)
    (lq : ∀ a ∈ L.getLast?,G.Adj a q)
    (qr : ∀ b ∈ R.head?,G.Adj q b)
    (apart : Disjoint L.toFinset R.toFinset)
    (ql : q∉L.toFinset) (qn : q∉R.toFinset)
    (balance : 3∣L.length+R.length+1) :
    FactorOn G ((L.toFinset∪R.toFinset)∪{q}) := by
  have nod : (L++q::R).Nodup := by
    apply ln.append (List.nodup_cons.mpr ⟨fun m=>qn (List.mem_toFinset.mpr m),rn⟩)
    intro u ul ur
    rcases List.mem_cons.mp ur with e|p
    · exact ql (e ▸ List.mem_toFinset.mpr ul)
    · exact disjoint_left.mp apart (List.mem_toFinset.mpr ul) (List.mem_toFinset.mpr p)
  have path : (L++q::R).Chain' G.Adj := by
    refine lc.append (rc.cons' qr) ?_
    intro a h b j
    have z : q=b := by simpa using j
    exact z ▸ lq a h
  have n : 3∣(L++q::R).length := by
    simpa only [List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using balance
  have z := run_factor (L++q::R) nod path n
  have shape : (L++q::R).toFinset=(L.toFinset∪R.toFinset)∪{q} := by
    ext x
    simp [or_assoc,or_comm,or_left_comm]
  rwa [shape] at z

#print axioms runCover_factor
#print axioms joined_at_factor
end KelmansCactus.AtomicBridge.RemoteGapRunPacking
