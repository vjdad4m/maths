import ConditionalMass
namespace Graffiti384b.Donor
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The unsigned total suffices for an actual sample at the increased
raw repair budget. The fixed omitted receivers R can all use the fixed
omitted donors D, which may be shared. -/
theorem batch_at_budget (F X R D : Finset V) (fx : Disjoint F X) (rd : Disjoint R D)
    (away : Disjoint (R∪D) (F∪X))
    (noSeed : ∀ v∈R∪D,nbr G v (F∪X)<2)
    (restore : ∀ v∈R,2≤nbr G v F+nbr G v D)
    {b cap : ℕ} (pos : 0<b)
    (budget : (∑ v,loss G F X b v)<(cap+R.card+1)*X.card.choose b) :
    ∃k∈X.powersetCard b,
      (deficient G (F∪k)).card≤cap+R.card ∧ R∪D⊆deficient G (F∪k) ∧
      gamma G≤F.card+b+cap := by
  classical
  obtain ⟨k,kb,cheap⟩ : ∃k∈X.powersetCard b,(deficient G (F∪k)).card≤cap+R.card := by
    by_contra! no
    have lower := sum_le_sum (s:=X.powersetCard b) (fun k hk => Nat.succ_le_of_lt (no k hk))
    rw [total_loss G F X fx pos] at lower
    simpa only [sum_const,smul_eq_mul,card_powersetCard,Nat.mul_comm] using
      (show False from (not_lt_of_ge (by simpa [Nat.mul_comm] using lower)) budget)
  obtain ⟨sub,sz⟩ := mem_powersetCard.mp kb
  have mono (v : V) {a b : Finset V} (inc : a⊆b) : nbr G v a≤nbr G v b :=
    card_le_card (filter_subset_filter _ inc)
  have inc : F∪k⊆F∪X := union_subset_union Subset.rfl sub
  have allBad : R∪D⊆deficient G (F∪k) := fun v vm => mem_filter.mpr ⟨mem_univ _,
    fun m => disjoint_left.mp away vm (inc m),
    lt_of_le_of_lt (mono v inc) (noSeed v vm)⟩
  have subR := (show R⊆R∪D from subset_union_left).trans allBad
  have subD : D⊆deficient G (F∪k)\R := fun v vm => mem_sdiff.mpr
    ⟨allBad (mem_union_right _ vm),fun r => disjoint_left.mp rd r vm⟩
  have good := batch_repair_saves G (F∪k) R subR (fun v vm =>
    (restore v vm).trans (Nat.add_le_add (mono v subset_union_left) (mono v subD)))
  change gamma G≤(F∪k).card+(deficient G (F∪k)).card-R.card at good
  rw [card_union_of_disjoint (fx.mono_right sub),sz] at good
  exact ⟨k,kb,cheap,allBad,by omega⟩

/-- For one oriented edge the same numerical test forces a sample in which
both endpoints need repair, the recipient has exactly one seed neighbor,
and the original raw repair count is at most cap + 1. -/
theorem pair_at_budget (F X : Finset V) (fx : Disjoint F X) {u v : V} (edge : G.Adj u v)
    (outU : u∉F∪X) (outV : v∉F∪X) (one : nbr G u F=1)
    (uCap : nbr G u (F∪X)<2) (vCap : nbr G v (F∪X)<2)
    {b cap : ℕ} (pos : 0<b) (budget : (∑x,loss G F X b x)<(cap+2)*X.card.choose b) :
    ∃ k∈X.powersetCard b, u∈deficient G (F∪k) ∧ v∈deficient G (F∪k) ∧
      nbr G u (F∪k)=1 ∧ (deficient G (F∪k)).card≤cap+1 ∧ gamma G≤F.card+b+cap := by
  have dis : Disjoint ({u}:Finset V) {v} := by simp [edge.ne.symm]
  have none : Disjoint (({u}:Finset V)∪{v}) (F∪X) := by simpa [disjoint_left] using And.intro outU outV
  have cov : ∀ x∈({u}:Finset V)∪{v},nbr G x (F∪X)<2 := by simpa using And.intro uCap vCap
  have recv : ∀x∈({u}:Finset V),2≤nbr G x F+nbr G x {v} := by
    intro x m; obtain rfl := mem_singleton.mp m
    have eq : ({v}:Finset V).filter (G.Adj x)={v} := filter_true_of_mem (fun w wm => (mem_singleton.mp wm) ▸ edge)
    rw [one]; simp [nbr,eq]
  obtain ⟨k,kb,cheap,inside,up⟩ := batch_at_budget G F X {u} {v} fx dis none cov recv pos (cap:=cap)
    (by simpa [Nat.add_assoc] using budget)
  have ub := inside (mem_union_left _ (mem_singleton_self u))
  have vb := inside (mem_union_right _ (mem_singleton_self v))
  have lower : nbr G u F≤nbr G u (F∪k) := card_le_card (filter_subset_filter _ subset_union_left)
  have lim := (mem_filter.mp ub).2.2
  exact ⟨k,kb,ub,vb,by omega,by simpa using cheap,up⟩

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.batch_at_budget
#print axioms Graffiti384b.Donor.pair_at_budget
