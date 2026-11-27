import RemoteGapRunPacking

namespace KelmansCactus.AtomicBridge.RemotePhaseChordRepair
open SimpleGraph Finset
open SquareCap (FactorOn)
open RemoteGapRunPacking (run_factor)
open RemoteVacancyRails (factor_disjUnion)
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- One extra edge can repair two leftover arcs of lengths 1 and 2 modulo 3.
The longer arc is split at b into two divisible runs; the bridge joins b
to the endpoint x of the other arc. Extra adjacency is irrelevant. -/
theorem chord_repairs_arcs (L R T : List V) (b x y : V)
    (distinct : (L ++ b :: R ++ x :: y :: T).Nodup)
    (first : (L ++ b :: R).Chain' G.Adj)
    (second : (x :: y :: T).Chain' G.Adj)
    (bridge : G.Adj b x)
    (dl : 3 ∣ L.length) (dr : 3 ∣ R.length) (dt : 3 ∣ T.length) :
    FactorOn G (L ++ b :: R ++ x :: y :: T).toFinset := by
  have reorder : (L ++ b :: R ++ x :: y :: T).Perm ((L ++ b :: x :: y :: T) ++ R) := by
    simpa only [List.append_assoc,List.cons_append] using
      (List.perm_append_comm (l₁ := R) (l₂ := x :: y :: T)).append_left (L ++ [b])
  have newNod := reorder.nodup distinct
  have cut : (L ++ [b] ++ R).Chain' G.Adj := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using first
  have l := (List.chain'_append.mp cut).1
  have rr := (List.chain'_append.mp cut).2.1
  have merged : ((L ++ [b]) ++ x :: y :: T).Chain' G.Adj := by
    apply l.append second
    intro u hu v hv
    have e₁ : b = u := by simpa using hu
    have e₂ : x = v := by simpa using hv
    simpa [←e₁,←e₂] using bridge
  have ndA := (List.nodup_append.mp newNod).1
  have ndB := (List.nodup_append.mp newNod).2.1
  have apart : Disjoint (L ++ b :: x :: y :: T).toFinset R.toFinset := by
    apply disjoint_left.mpr
    intro u hu hv
    exact (List.nodup_append.mp newNod).2.2
      (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hv)
  have ndM : (L ++ b :: x :: y :: T).Chain' G.Adj := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using merged
  have divM : 3 ∣ (L ++ b :: x :: y :: T).length := by
    simp only [List.length_append,List.length_cons]
    omega
  have packed := factor_disjUnion (run_factor _ ndA ndM divM) (run_factor _ ndB rr dr) apart
  have eq : (L ++ b :: R ++ x :: y :: T).toFinset =
      (L ++ b :: x :: y :: T).toFinset ∪ R.toFinset := by
    rw [←List.toFinset_append]
    ext z
    simpa only [List.mem_toFinset] using (reorder.mem_iff (a:=z))
  exact eq ▸ packed

#print axioms chord_repairs_arcs
end KelmansCactus.AtomicBridge.RemotePhaseChordRepair
