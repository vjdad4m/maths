import TreeBudget
import TreeRepairData

open private validFull lift_full_cert from SplitTipsLocal
open private inner_index_cases from NormalizedDepleted

namespace Graffiti199Depleted.TreeRepair

open SimpleGraph Graffiti199K2.NearPacking.Depleted

def highLabel (k : K) : Bool := (k != 0) && (k != 4) && decide (k.val < 8)

private theorem high_inside (i : I) (hi : high i = true) : highLabel (inside i) = true := by
  revert i
  decide

def potential (r : Row) (a b : K) : Bool :=
  has (edges r false) a b ||
    ((a != b) && highLabel a && highLabel b && !(has forbidden a b) && !(has [(3,7)] a b))

private def lowerAdj (E : List (K × K)) (w : ForcingStep) (i j : Fin 6) : Prop :=
  has E (w.witness i) (w.witness j) = true ∧ j < i

private instance (E : List (K × K)) (w : ForcingStep) (i j : Fin 6) :
    Decidable (lowerAdj E w i j) := inferInstanceAs (Decidable (_ ∧ _))

def validStep (r : Row) (E : List (K × K)) (w : ForcingStep) : Bool :=
  decide (∀ i j : Fin 6, w.witness i = w.witness j → i = j) &&
  decide (∀ i : Fin 6, i ≠ 0 → ∃ j : Fin 6, lowerAdj E w i j ∧
    ∀ k : Fin 6, lowerAdj E w i k → k = j) &&
  decide (∀ i j : Fin 6, potential r (w.witness i) (w.witness j) = true →
    has E (w.witness i) (w.witness j) = true ∨ has [w.chord] (w.witness i) (w.witness j) = true)

def validRepair (r : Row) (E : List (K × K)) : List ForcingStep → Bool
  | [] => true
  | w :: ws => validStep r E w && validRepair r (E ++ [w.chord]) ws

def repairedEdges (r : Row) := edges r false ++ (repair r).map ForcingStep.chord

def specialRows : List Nat := [18,19,20,21,22,23]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem baseline_or_repair :
    ∀ (r : Row) (b : Bool), possible r = true →
      (blocked r b).card ≤ 2 ∨ (b = false ∧ r.val ∈ specialRows) := by
  intro r
  fin_cases r <;> decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem repair_checked :
    ∀ r : Row, r.val ∈ specialRows →
      validRepair r (edges r false) (repair r) = true ∧
      ∀ i : I, high i = true →
        validFull (repairedEdges r) (route r i) ((route r i).headD 0) (inside i) = true := by
  intro r
  fin_cases r <;> decide

private theorem known_neighbor (r : Row) (a : K) (ns : List K)
    (h : innerLowNeighbors r a = some ns) {b : K} (hb : b ∈ ns) :
    has (edges r false) a b = true := by
  fin_cases a
  · have eq : [1,2,3] = ns := Option.some.inj h
    rw [← eq] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl <;> simp [has,edges,List.contains_iff_mem]
  · cases h
  · cases h
  · cases h
  · have eq : [5,6,7] = ns := Option.some.inj h
    rw [← eq] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl <;> simp [has,edges,List.contains_iff_mem]
  · cases h
  · cases h
  · cases h
  · have eq : [9,inside (halves r).1,inside (halves r).2.1] = ns := Option.some.inj h
    rw [← eq] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl <;> simp [has,edges,List.contains_iff_mem]
  · have eq : [8,inside (halves r).2.2.1,inside (halves r).2.2.2] = ns := Option.some.inj h
    rw [← eq] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl <;> simp [has,edges,List.contains_iff_mem]

variable {V : Type*} {G : SimpleGraph V} {loss : Bool}

private theorem upperAdj (L : NormalizedDepleted G loss) (loose : ¬ G.Adj (L.inner 3) (L.inner 7))
    {a b : K} (adj : G.Adj (L.inner a) (L.inner b)) : potential L.row a b = true := by
  rcases inner_index_cases L.row a with ⟨i,rfl,hi⟩|⟨ns,eq⟩
  · rcases inner_index_cases L.row b with ⟨j,rfl,hj⟩|⟨ns,eq⟩
    · have off : has forbidden (inside i) (inside j) = false := by
        cases h : has forbidden (inside i) (inside j)
        · rfl
        · simp only [has,Bool.or_eq_true,List.contains_iff_mem] at h
          exact (h.elim (fun e => L.innerNonedges _ _ e adj)
            (fun e => L.innerNonedges _ _ e adj.symm)).elim
      have apart : has [(3,7)] (inside i) (inside j) = false := by
        cases h : has [(3,7)] (inside i) (inside j)
        · rfl
        · simp only [has,Bool.or_eq_true,List.contains_iff_mem,List.mem_singleton] at h
          rcases h with h|h
          · obtain ⟨hi',hj'⟩ := Prod.mk.inj h
            exact (loose (hi' ▸ hj' ▸ adj)).elim
          · obtain ⟨hj',hi'⟩ := Prod.mk.inj h
            exact (loose (hi' ▸ hj' ▸ adj).symm).elim
      have ne : inside i ≠ inside j := fun eq => adj.ne (congrArg L.inner eq)
      simp [potential,ne,high_inside _ hi,high_inside _ hj,off,apart]
    · obtain ⟨k,mem,key⟩ := L.innerLow _ _ eq _ adj.symm
      have e := L.inner.injective key
      have covered : has (edges L.row false) b (inside i) = true := e ▸ known_neighbor _ _ _ eq mem
      have symm : has (edges L.row false) (inside i) b = true := by
        simpa only [has,Bool.or_comm] using covered
      simp [potential,symm]
  · obtain ⟨k,mem,key⟩ := L.innerLow _ _ eq _ adj
    have e := L.inner.injective key
    have covered : has (edges L.row false) a b = true := e ▸ known_neighbor _ _ _ eq mem
    simp [potential,covered]

private theorem lower_lift (f : K ↪ V) (E : List (K × K))
    (lower : ∀ a b, (a,b) ∈ E → G.Adj (f a) (f b))
    {a b : K} (h : has E a b = true) : G.Adj (f a) (f b) := by
  simp only [has,Bool.or_eq_true,List.contains_iff_mem] at h
  exact h.elim (lower a b) (fun e => (lower b a e).symm)

variable [Fintype V]

private theorem force_chord (f : K ↪ V) {r : Row} (E : List (K × K)) (w : ForcingStep)
    (bound : Catalogue.treeNumber G ≤ 5)
    (lower : ∀ a b, (a,b) ∈ E → G.Adj (f a) (f b))
    (upper : ∀ a b, G.Adj (f a) (f b) → potential r a b = true)
    (cert : validStep r E w = true) :
    G.Adj (f w.chord.1) (f w.chord.2) := by
  classical
  simp only [validStep,Bool.and_eq_true,decide_eq_true_eq] at cert
  obtain ⟨⟨inj,earlier⟩,cover⟩ := cert
  by_contra no
  let q : Fin 6 ↪ K := ⟨w.witness,fun _ _ eq => inj _ _ eq⟩
  have sub (i j : Fin 6) (h : G.Adj (f (q i)) (f (q j))) :
      has E (q i) (q j) = true := by
    rcases cover i j (upper _ _ h) with yes|edge
    · exact yes
    · simp only [has,Bool.or_eq_true,List.contains_iff_mem,List.mem_singleton] at edge
      rcases edge with e|e
      · change G.Adj (f (w.witness i)) (f (w.witness j)) at h
        have ea : w.witness i = w.chord.1 := congrArg Prod.fst e
        have eb : w.witness j = w.chord.2 := congrArg Prod.snd e
        rw [ea,eb] at h
        exact (no h).elim
      · have h' := h.symm
        change G.Adj (f (w.witness j)) (f (w.witness i)) at h'
        have ea : w.witness j = w.chord.1 := congrArg Prod.fst e
        have eb : w.witness i = w.chord.2 := congrArg Prod.snd e
        rw [ea,eb] at h'
        exact (no h').elim
  have size := Catalogue.six_le_treeNumber_of_ordering (G := G) (q.trans f) (by
    intro i hi
    obtain ⟨j,jh,only⟩ := earlier i hi
    exact ⟨j,lower_lift f E lower jh.1,jh.2,fun k adj lt => only k ⟨sub _ _ adj,lt⟩⟩)
  omega

private theorem apply_repair (f : K ↪ V) {r : Row} (E : List (K × K))
    (steps : List ForcingStep) (bound : Catalogue.treeNumber G ≤ 5)
    (lower : ∀ a b, (a,b) ∈ E → G.Adj (f a) (f b))
    (upper : ∀ a b, G.Adj (f a) (f b) → potential r a b = true)
    (cert : validRepair r E steps = true) :
    ∀ a b, (a,b) ∈ E ++ steps.map ForcingStep.chord → G.Adj (f a) (f b) := by
  induction steps generalizing E with
  | nil => simpa
  | cons step rest ih =>
    simp only [validRepair,Bool.and_eq_true] at cert
    obtain ⟨first,again⟩ := cert
    have next (a b : K) (h : (a,b) ∈ E ++ [step.chord]) : G.Adj (f a) (f b) := by
      rcases List.mem_append.mp h with ed|ed
      · exact lower a b ed
      · have eq := List.mem_singleton.mp ed
        have same : (a,b) = (step.chord.1,step.chord.2) := eq
        obtain ⟨ea,eb⟩ := Prod.mk.inj same
        rw [ea,eb]
        exact force_chord f E step bound lower upper first
    intro a b h
    apply ih (E ++ [step.chord]) next again a b
    simpa only [List.append_assoc,List.singleton_append,List.map_cons] using h

/-- Every high endpoint is available in the six exceptional rows once
the original graph has induced tree number at most five. -/
theorem repaired_path_at_any_high (L : NormalizedDepleted G loss) (bound : Catalogue.treeNumber G ≤ 5)
    (loose : ¬ G.Adj (L.inner 3) (L.inner 7)) (row : L.row.val ∈ specialRows)
    {i : I} (hi : high i = true) :
    ∃ p : PathOn G (innerRegion L.inner), p.last = L.inner (inside i) := by
  obtain ⟨good,routeOK⟩ := repair_checked L.row row
  have lifted := apply_repair L.inner (edges L.row false) (repair L.row) bound
    (fun a b e => L.innerEdges a b (by simpa [edges] using e)) (fun _ _ => upperAdj L loose) good
  obtain ⟨p,_,last⟩ := lift_full_cert L.inner (repairedEdges L.row) lifted (routeOK i hi)
  exact ⟨p,last⟩

#print axioms baseline_or_repair
#print axioms repaired_path_at_any_high

end Graffiti199Depleted.TreeRepair
