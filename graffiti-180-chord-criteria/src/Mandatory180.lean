import Assembly180
import Critical180
import StrongDegree179

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Converse180 Rooted180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Deleting the eligibility of a vertex lowers the optimum precisely when
that vertex is eligible and every optimal tree uses it as a leaf. -/
theorem mandatory_iff (hc : G.Connected) (U : Finset V) (x : V) :
    weightedLeaves G (U.erase x) < weightedLeaves G U ↔
      x∈U ∧ ∀ K ≤ G, K.IsTree → (U ∩ leaves K).card=weightedLeaves G U → x∈leaves K := by
  classical
  constructor
  · intro drop
    refine ⟨?_,?_⟩
    · by_contra out
      rw [erase_eq_of_not_mem out] at drop
      exact (lt_irrefl _ drop)
    · intro K sub kt eq
      by_contra out
      have b : (U.erase x ∩ leaves K).card ≤ weightedLeaves G (U.erase x) :=
        le_sup (f:=fun T => (U.erase x ∩ leaves T).card) (mem_filter.mpr ⟨mem_univ _,sub,kt⟩)
      rw [erase_inter,erase_eq_of_not_mem (fun h => out (mem_inter.mp h).2),eq] at b
      omega
  · rintro ⟨xu,must⟩
    obtain ⟨K,sub,kt,eq⟩ := tree_opt G hc (U.erase x)
    have b : (U ∩ leaves K).card ≤ weightedLeaves G U :=
      le_sup (f:=fun T => (U ∩ leaves T).card) (mem_filter.mpr ⟨mem_univ _,sub,kt⟩)
    have cnt := card_trim (U ∩ leaves K) x
    rw [erase_inter] at eq
    by_contra! no
    have same : (U ∩ leaves K).card = weightedLeaves G U := by omega
    have xl := must _ sub kt same
    rw [weight,if_pos (mem_inter.mpr ⟨xu,xl⟩)] at cnt
    omega

/-- Decorate every ineligible vertex and the specified eligible vertex by
one pendant, then apply Strong179's maximum-degree leaf theorem. -/
theorem degree_erased [DecidableRel G.Adj] (hc : G.Connected) (hn : 1<Fintype.card V)
    (U : Finset V) (x : V) (xu : x∈U) :
    G.degree x ≤ weightedLeaves G (U.erase x)+(univ \ U).card := by
  classical
  let D := insert x (univ \ U)
  let H := decorate G D
  let z : ↥D := ⟨x,mem_insert_self _ _⟩
  have cardD : D.card=(univ \ U).card+1 := card_insert_of_not_mem (fun h => (mem_sdiff.mp h).2 xu)
  have cnt : Fintype.card (Deco D)=Fintype.card V+D.card := by simp [Deco]
  letI : Nontrivial (Deco D) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hd := Graffiti179.Strong.degree_le_maxLeaves H (deco_layers G hc x D).1 (.inl x)
  have nbor : (G.neighborFinset x).disjSum ({z} : Finset ↥D) ⊆ H.neighborFinset (.inl x) := by
    rintro (a|a) h
    · exact (H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp (inl_mem_disjSum.mp h))
    · have e := mem_singleton.mp (inr_mem_disjSum.mp h)
      exact (H.mem_neighborFinset _ _).mpr (e ▸ (show H.Adj (.inl x) (.inr z) from rfl))
  have deg := card_le_card nbor
  rw [card_disjSum,card_singleton,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at deg
  have upper := deco_leaves G hn D univ
  have e : (univ : Finset V).disjSum (univ : Finset ↥D)=univ := by ext v; cases v <;> simp
  have rem : univ \ D = U.erase x := by ext v; simp [D]
  rw [e,weighted_all,rem,cardD] at upper
  change H.degree (.inl x) ≤ maxLeaves H at hd
  change maxLeaves H ≤ _ at upper
  omega

/-- Necessary degree ceiling on each mandatory endpoint in a sharp local
state. The intersection counts overlap and the last unit is the root
excluded from its union. -/
theorem tight_degree [DecidableRel G.Adj] (hc : G.Connected) (hn : 1<Fintype.card V)
    (A P : Finset V) (r x : V)
    (tight : weightedLeaves G (eligible A P r)+bipartiteNum G=1+A.card+P.card)
    (drop : weightedLeaves G ((eligible A P r).erase x)<weightedLeaves G (eligible A P r)) :
    G.degree x+bipartiteNum G ≤ Fintype.card V+(A ∩ P).card+
      (if r∈A ∪ P ∧ r∉A ∩ P then 1 else 0) := by
  classical
  let U := eligible A P r
  have xu := ((mandatory_iff G hc U x).mp drop).1
  have deg := degree_erased G hc hn U x xu
  have cnt := card_sdiff_add_card_eq_card (subset_univ U)
  rw [card_univ] at cnt
  have unioncard := card_union_add_card_inter A P
  have rem : U.card+(if r∈A ∪ P ∧ r∉A ∩ P then 1 else 0)=(A ∪ P).card := by
    by_cases a : r∈A <;> by_cases p : r∈P <;>
      simp only [U,eligible,mem_union,mem_inter,a,p,true_and,and_true,false_and,and_false,true_or,
        or_true,false_or,not_true_eq_false,not_false_eq_true,if_true,if_false,Nat.add_zero]
    all_goals first | exact card_erase_add_one (mem_union_left _ a) |
      exact card_erase_add_one (mem_union_right _ p) |
      rw [erase_eq_of_not_mem (by simp [a,p])]
  change weightedLeaves G U+bipartiteNum G=_ at tight
  change weightedLeaves G (U.erase x)<weightedLeaves G U at drop
  omega

#print axioms mandatory_iff
#print axioms degree_erased
#print axioms tight_degree
end Assembly180
