import Deficiency
import Mathlib.Tactic.Linarith

namespace RegularCover5174
open SimpleGraph Finset TriangleMatching1078 BullCover1125 RainbowCover1553
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At a selected endpoint, a neighbor on its own selected edge consumes one
unit of degree. Only excess above k+1 can contribute to Hall deficiency. -/
theorem degree_error {k : ℕ} (hk : 0 < k) (lower : ∀ v, k ≤ G.degree v) :
    edgeCoverNumber G ≤ 2 * lineDomination G + (∑ v : V, (G.degree v-(k+1))) / k := by
  classical
  have iso : IsolateFree G := by
    intro v
    have pos : 0 < (G.neighborFinset v).card := hk.trans_le (lower v)
    obtain ⟨w,hw⟩ := card_pos.mp pos
    exact ⟨w,(G.mem_neighborFinset _ _).mp hw⟩
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={n | ∃ D : Finset G.edgeSet,
    D.card=n ∧ Dominates G.lineGraph D}) ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination G at sz
  let ends (e : G.edgeSet) : Finset V := {e.val.out.1,e.val.out.2}
  let S := D.biUnion ends
  have incident {v} : v ∈ S ↔ ∃ e ∈ D, v ∈ e.val := by
    simp only [S,mem_biUnion]
    apply exists_congr
    intro e
    apply and_congr_right
    intro _
    have repr : s(e.val.out.1,e.val.out.2) = e.val := e.val.out_eq
    calc
      v ∈ ends e ↔ v ∈ s(e.val.out.1,e.val.out.2) := by
        simp only [ends,mem_insert,mem_singleton,Sym2.mem_iff]
      _ ↔ v ∈ e.val := iff_of_eq (congrArg (fun p : Sym2 V => v ∈ p) repr)
  have hits {v w} (adj : G.Adj v w) : v ∈ S ∨ w ∈ S := by
    obtain ⟨e,he,z,hz,mem⟩ := (dominates_iff G D).mp dom ⟨s(v,w),adj⟩
    rcases Sym2.mem_iff.mp mem with rfl|rfl
    · exact Or.inl (incident.mpr ⟨e,he,hz⟩)
    · exact Or.inr (incident.mpr ⟨e,he,hz⟩)
  have size : S.card ≤ 2 * lineDomination G := calc
    _ ≤ ∑ e ∈ D, (ends e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ D, 2 := sum_le_sum (fun _ _ => (card_insert_le _ _).trans (by simp))
    _ = _ := by simp [sz,Nat.mul_comm]
  have demand (v : V) (hv : v ∉ S) : k ≤ (S.filter (G.Adj v)).card := by
    apply (lower v).trans (card_le_card ?_)
    intro u hu
    have adj := (G.mem_neighborFinset v u).mp hu
    exact mem_filter.mpr ⟨(hits adj).resolve_left hv,adj⟩
  have internal (v : V) (hv : v ∈ S) : ∃ w ∈ S, G.Adj v w := by
    obtain ⟨e,he,mem⟩ := incident.mp hv
    obtain ⟨w,eq⟩ := Sym2.mem_iff_exists.mp mem
    have vw : G.Adj v w := show s(v,w) ∈ G.edgeSet from eq ▸ e.property
    exact ⟨w,incident.mpr ⟨e,he,by rw [eq]; exact Sym2.mem_iff.mpr (Or.inr rfl)⟩,vw⟩
  have localCost (v : V) (hv : v ∈ S) :
      ((G.neighborFinset v) \ S).card-k ≤ G.degree v-(k+1) := by
    obtain ⟨w,hw,adj⟩ := internal v hv
    have mem := (G.mem_neighborFinset v w).mpr adj
    have sub : G.neighborFinset v \ S ⊆ (G.neighborFinset v).erase w := by
      intro u hu
      exact mem_erase.mpr ⟨fun eq => (mem_sdiff.mp hu).2 (eq ▸ hw),(mem_sdiff.mp hu).1⟩
    have cap := card_le_card sub
    rw [card_erase_of_mem mem,G.card_neighborFinset_eq_degree] at cap
    omega
  have excess : crossExcess G S k ≤ ∑ v : V, (G.degree v-(k+1)) :=
    (sum_le_sum localCost).trans (sum_le_sum_of_subset (subset_univ S))
  exact (cover_of_k_dominating G iso S hk demand).trans
    (Nat.add_le_add size (Nat.div_le_div_right excess))

theorem almost_regular {k : ℕ} (hk : 0 < k) (lower : ∀ v, k ≤ G.degree v)
    (upper : ∀ v, G.degree v ≤ k+1) : edgeCoverNumber G ≤ 2 * lineDomination G := by
  have zero : (∑ v : V, (G.degree v-(k+1))) = 0 :=
    sum_eq_zero (fun v _ => Nat.sub_eq_zero_of_le (upper v))
  simpa [zero] using degree_error G hk lower

theorem regular_bound [Nonempty V] (iso : IsolateFree G) {k : ℕ} (reg : G.IsRegularOfDegree k) :
    edgeCoverNumber G ≤ 2 * lineDomination G := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨w,vw⟩ := iso v
  have hp := card_pos.mpr ⟨w,(G.mem_neighborFinset v w).mpr vw⟩
  rw [G.card_neighborFinset_eq_degree,reg v] at hp
  exact almost_regular G hp (fun x => (reg x).ge) (fun x => (reg x).le.trans (Nat.le_succ _))

/-- There is no lower-order hypothesis. On the empty graph the numerical
antecedent is false, independently of the convention for regularity. -/
theorem row5174 {r : ℕ} (numeric : edgeCoverValue G = some r)
    (strict : (lineDomination G : ℚ) < (1/2 : ℚ)*r) : ¬ ∃ k, G.IsRegularOfDegree k := by
  classical
  rintro ⟨k,reg⟩
  by_cases iso : IsolateFree G
  · have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,iso] using numeric
    have h : r ≤ 2 * lineDomination G := by
      by_cases inhabited : Nonempty V
      · letI := inhabited
        simpa only [eq] using regular_bound G iso reg
      · have zero : edgeCoverNumber G ≤ 0 := Nat.sInf_le
          ⟨∅,rfl,fun v => False.elim (inhabited ⟨v⟩)⟩
        omega
    have cast : (r : ℚ) ≤ 2*(lineDomination G : ℚ) := by exact_mod_cast h
    linarith
  · simp [edgeCoverValue,iso] at numeric

#print axioms degree_error
#print axioms almost_regular
#print axioms regular_bound
#print axioms row5174
end RegularCover5174
