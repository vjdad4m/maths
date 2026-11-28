import ChoiceMass
namespace Graffiti384b.FiveChoice
open Finset SimpleGraph Four29
variable {V : Type*} [DecidableEq V]

/-- Upper bound on the number of samples missing one quota, computed from
the full carrier, its fixed part and the exact first moment. -/
def risk (L : Finset (Finset V)) (B U : Finset V) (k d : ℕ) :=
  let N := U.card.choose k
  let s := (kept L (B∪U)).card
  if d≤(kept L B).card then 0 else
    if d≤s then min N ((s*N-mass L B U k)/(s-d+1)) else N

theorem risk_bound (L : Finset (Finset V)) (B U : Finset V) (k d : ℕ) :
    ((U.powersetCard k).filter (fun S => (kept L (B∪S)).card<d)).card≤risk L B U k d := by
  classical
  let P := U.powersetCard k
  let s := (kept L (B∪U)).card
  let bad := P.filter (fun S => (kept L (B∪S)).card<d)
  have num := card_powersetCard k U
  change P.card=U.card.choose k at num
  unfold risk
  split
  · rename_i fixed
    have empty : bad=∅ := eq_empty_of_forall_not_mem (fun S sm => by
      have more := card_le_card (kept_mono (L:=L) (subset_union_left (s₂:=S) (s₁:=B)))
      exact (not_lt_of_ge (fixed.trans more)) (mem_filter.mp sm).2)
    change bad.card≤0; rw [empty,card_empty]
  have within : bad.card≤U.card.choose k := (card_filter_le ..).trans_eq num
  change bad.card ≤ if d≤s then min (U.card.choose k) ((s*U.card.choose k-mass L B U k)/(s-d+1)) else U.card.choose k
  split
  · rename_i enough
    apply le_min within
    change bad.card≤(s*U.card.choose k-mass L B U k)/(s-d+1)
    apply (Nat.le_div_iff_mul_le (by omega : 0<s-d+1)).mpr
    have each (S : Finset V) (sm : S∈P) :
        (kept L (B∪S)).card+(if S∈bad then s-d+1 else 0)≤s := by
      have upper : (kept L (B∪S)).card≤s := card_le_card (kept_mono (union_subset_union_right (mem_powersetCard.mp sm).1))
      by_cases low : S∈bad
      · rw [if_pos low]; have below := (mem_filter.mp low).2
        change d≤s at enough
        omega
      · rwa [if_neg low,Nat.add_zero]
    have total := sum_le_sum each
    rw [sum_add_distrib] at total
    have on : (∑S∈P,if S∈bad then s-d+1 else 0)=bad.card*(s-d+1) := by
      rw [←sum_filter]
      have eq : P.filter (·∈bad)=bad := by ext S; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨(mem_filter.mp h).1,h⟩⟩
      rw [eq,sum_const,nsmul_eq_mul,Nat.cast_id]
    change (∑S∈U.powersetCard k,(kept L (B∪S)).card)+_≤_ at total
    rw [total_score,on,sum_const,nsmul_eq_mul,Nat.cast_id,num,Nat.mul_comm (U.card.choose k) s] at total
    omega
  · exact within

/-- The four individual bounds can be combined without assuming independent
failures. -/
theorem joint_choice (A B U : Finset V) (L : V→Finset (Finset V)) (k : ℕ) (need : V→ℕ)
    (slack : (∑a∈A,risk (L a) B U k (need a))<U.card.choose k) :
    ∃S∈U.powersetCard k,∀a∈A,need a≤(kept (L a) (B∪S)).card := by
  classical
  let bad := fun a => (U.powersetCard k).filter (fun S => (kept (L a) (B∪S)).card<need a)
  have cap := (card_biUnion_le (s:=A) (t:=bad)).trans (sum_le_sum (fun a _ => risk_bound (L a) B U k (need a)))
  obtain ⟨S,sm,good⟩ := not_subset.mp (fun sub : U.powersetCard k⊆A.biUnion bad => by
    have sz := card_le_card sub; rw [card_powersetCard] at sz; omega)
  exact ⟨S,sm,fun a am => Nat.le_of_not_gt (fun low => good (mem_biUnion.mpr ⟨a,am,mem_filter.mpr ⟨sm,low⟩⟩))⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem joint_selection (t : (types G).card=29) (h : (high G).card=27) (q : (nonleaves G).card=29)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (F U : Finset V) (fp : F⊆pool G e f) (up : U⊆pool G e f) (k : ℕ) (five : F.card+k≤5)
    {a : V} (ar : a∈roots G e f)
    (slack : (∑v∈roots G e f,risk (link G v) (base G e f∪F) U k (if v=a then 13 else 2))<U.card.choose k) :
    gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have D := data_of_failure G t h q bad de df ne
  obtain ⟨S,sm,ok⟩ := joint_choice (roots G e f) (base G e f∪F) U (link G) k _ slack
  obtain ⟨su,sz⟩ := mem_powersetCard.mp sm
  have limit := card_union_le F S
  obtain ⟨K,inc,kp,ks⟩ := exists_subsuperset_card_eq (union_subset fp (su.trans up))
    (by omega : (F∪S).card≤5) (by rw [D.poolSize]; decide)
  have atK (v : V) (vm : v∈roots G e f) :
      (if v=a then 13 else 2)≤score G e f K v := by
    have lower := ok v vm
    rw [union_assoc] at lower
    exact lower.trans (card_le_card (kept_mono (union_subset_union_right inc)))
  have maj : 13≤score G e f K a := by simpa only [if_pos rfl] using atK a ar
  exact (not_lt_of_ge (five_chosen G t h q de df ne kp ks (fun v vm => by
    by_cases eq : v=a
    · subst v; omega
    · simpa only [if_neg eq] using atK v vm) ar maj)) bad
end Graffiti384b.FiveChoice
#print axioms Graffiti384b.FiveChoice.risk_bound
#print axioms Graffiti384b.FiveChoice.joint_choice
#print axioms Graffiti384b.FiveChoice.joint_selection
