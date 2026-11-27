import RemoteGapRunPacking

namespace KelmansCactus.AtomicBridge.RemoteDiagonalEarPhases
open Finset SimpleGraph
open RemoteVacancyRails (factor_disjUnion)
open RemoteGapRunPacking (run_factor)
open SquareCap (FactorOn)
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem arm_chain {p : V} {E A : List V}
    (ec : E.Chain' G.Adj) (ac : A.Chain' G.Adj)
    (ep : ∀ e∈E.head?,G.Adj p e) (ap : ∀ a∈A.head?,G.Adj p a) :
    (E.reverse++p::A).Chain' G.Adj := by
  apply (List.chain'_reverse.mpr (ec.imp fun _ _ h=>h.symm)).append (ac.cons' ap)
  intro x hx y hy
  rw [List.getLast?_reverse] at hx
  have e : p=y := by simpa using hy
  exact e ▸ (ep x hx).symm

/-- Split a mixed diagonal cycle at two ports and append the two whole ears,
instead of assuming either ear's leftover singleton can always be rescued. -/
theorem factor_two_ear_arcs {p q : V} (E F A B : List V)
    (nodup : (p::q::(E++F++A++B)).Nodup)
    (ec : E.Chain' G.Adj) (fc : F.Chain' G.Adj)
    (ac : A.Chain' G.Adj) (bc : B.Chain' G.Adj)
    (pe : ∀ e∈E.head?,G.Adj p e) (qf : ∀ f∈F.head?,G.Adj q f)
    (pa : ∀ a∈A.head?,G.Adj p a) (qb : ∀ b∈B.head?,G.Adj q b)
    (aDiv : 3∣E.length+1+A.length) (bDiv : 3∣F.length+1+B.length) :
    FactorOn G (p::q::(E++F++A++B)).toFinset := by
  let L := E.reverse++p::A
  let R := F.reverse++q::B
  have perm : (p::q::(E++F++A++B)).Perm (L++R) := by
    apply Multiset.coe_eq_coe.mp
    simp only [L,R,←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,
      Multiset.coe_reverse]
    ac_rfl
  have nd := List.nodup_append.mp (perm.nodup_iff.mp nodup)
  have lFactor := run_factor L nd.1 (arm_chain ec ac pe pa)
    (by simpa [L,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using aDiv)
  have rFactor := run_factor R nd.2.1 (arm_chain fc bc qf qb)
    (by simpa [R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bDiv)
  have apart : Disjoint L.toFinset R.toFinset := by
    rw [Finset.disjoint_left]
    intro x xl xr
    exact nd.2.2 (List.mem_toFinset.mp xl) (List.mem_toFinset.mp xr)
  have f := factor_disjUnion lFactor rFactor apart
  rwa [List.toFinset_eq_of_perm _ _ perm,List.toFinset_append]

/-- Useful exact residue slice: when ears of orders 1 and 2 mod 3 are
attached to the two exposed ports, all admissible gap phases except 2+2
can be tiled by the two complete appended arms. This does not assert a
full obstruction in the 2+2 phase if extra graph edges exist. -/
theorem factor_one_two {p q : V} (E F A B : List V)
    (nodup : (p::q::(E++F++A++B)).Nodup)
    (ec : E.Chain' G.Adj) (fc : F.Chain' G.Adj)
    (ac : A.Chain' G.Adj) (bc : B.Chain' G.Adj)
    (pe : ∀ e∈E.head?,G.Adj p e) (qf : ∀ f∈F.head?,G.Adj q f)
    (pa : ∀ a∈A.head?,G.Adj p a) (qb : ∀ b∈B.head?,G.Adj q b)
    (qa : ∀ a∈A.getLast?,G.Adj q a) (pb : ∀ b∈B.getLast?,G.Adj p b)
    (eRem : E.length%3=1) (fRem : F.length%3=2)
    (total : 3∣E.length+F.length+A.length+B.length+2)
    (phase : ¬(A.length%3=2 ∧ B.length%3=2)) :
    FactorOn G (p::q::(E++F++A++B)).toFinset := by
  have cases : (A.length%3=1 ∧ B.length%3=0) ∨
      (A.length%3=0 ∧ B.length%3=1) := by omega
  rcases cases with c|c
  · exact factor_two_ear_arcs E F A B nodup ec fc ac bc pe qf pa qb (by omega) (by omega)
  · have perm : (p::q::(E++F++A++B)).Perm (p::q::(E++F++B.reverse++A.reverse)) := by
      apply Multiset.coe_eq_coe.mp
      simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_reverse]
      ac_rfl
    have ac' : A.reverse.Chain' G.Adj := List.chain'_reverse.mpr (ac.imp fun _ _ h=>h.symm)
    have bc' : B.reverse.Chain' G.Adj := List.chain'_reverse.mpr (bc.imp fun _ _ h=>h.symm)
    have f := factor_two_ear_arcs E F B.reverse A.reverse
      (perm.nodup_iff.mp nodup) ec fc bc' ac' pe qf
      (by simpa only [List.head?_reverse] using pb)
      (by simpa only [List.head?_reverse] using qa)
      (by rw [List.length_reverse]; omega)
      (by rw [List.length_reverse]; omega)
    rwa [List.toFinset_eq_of_perm _ _ perm]

#print axioms factor_two_ear_arcs
#print axioms factor_one_two
end KelmansCactus.AtomicBridge.RemoteDiagonalEarPhases
