import PairTests180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Conflicting outside neighbors when the retained tips are assigned
their own colors. A common neighbor is charged only once. -/
noncomputable def conflicts (G : SimpleGraph V) (S T : Finset V) (c d : V→Bool) : Finset V :=
  S.filter (fun x => ∃ t∈T,G.Adj t x ∧ c x=d t)

theorem repair (G : SimpleGraph V) (X K : Finset V) (ind : Indep G K) (c d : V→Bool)
    (ok : ProperOn G (univ\X) c) :
    ∃ Z,TwoColor G Z ∧ K⊆Z ∧ Fintype.card V-Z.card≤
      (X\K).card+(conflicts G (univ\X) (X∩K) c d).card := by
  classical
  let F := conflicts G (univ\X) (X∩K) c d
  let M := (X\K)∪F
  let Z := univ\M
  let e (x : V) := if x∈X then d x else c x
  have keep : K⊆Z := by
    intro x xk
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    rintro m
    rcases mem_union.mp m with er|f
    · exact (mem_sdiff.mp er).2 xk
    · obtain ⟨t,tm,tx,_⟩ := (mem_filter.mp f).2
      exact ind t (mem_inter.mp tm).2 x xk tx.ne tx
  have ktip {t : V} (tm : t∈Z) (tx : t∈X) : t∈X∩K := by
    refine mem_inter.mpr ⟨tx,?_⟩
    by_contra tk
    exact (mem_sdiff.mp tm).2 (mem_union_left _ (mem_sdiff.mpr ⟨tx,tk⟩))
  have cross {x t : V} (xm : x∈Z) (xx : x∉X) (tm : t∈Z) (tx : t∈X) (ed : G.Adj t x) : c x≠d t := by
    intro eq
    have f : x∈F := mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,xx⟩,t,ktip tm tx,ed,eq⟩
    exact (mem_sdiff.mp xm).2 (mem_union_right _ f)
  have bi : TwoColor G Z := by
    apply (color_function ..).mpr
    refine ⟨e,fun x xm y ym xy => ?_⟩
    by_cases xx : x∈X <;> by_cases yx : y∈X
    · exact (ind x (mem_inter.mp (ktip xm xx)).2 y (mem_inter.mp (ktip ym yx)).2 xy.ne xy).elim
    · simpa [e,xx,yx] using Ne.symm (cross ym yx xm xx xy)
    · simpa [e,xx,yx] using cross xm xx ym yx xy.symm
    · simpa [e,xx,yx] using ok x (mem_sdiff.mpr ⟨mem_univ _,xx⟩) y (mem_sdiff.mpr ⟨mem_univ _,yx⟩) xy
  have sz := card_sdiff_add_card_eq_card (subset_univ M)
  rw [card_univ] at sz
  have cap : M.card≤(X\K).card+F.card := card_union_le ..
  exact ⟨Z,bi,keep,by change Fintype.card V-(univ\M).card≤(X\K).card+F.card;omega⟩

theorem budget_two (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (a b : V) (ne : a≠b) (bi : TwoColor G (univ\{a,b})) :
    2≤allowance G r p A ∧ 2<Fintype.card V := by
  have high : bipartiteNum G+1<Fintype.card V := by
    by_contra! small;exact bad (protected_rank_one G gc hn small r p A ai)
  have rk : Fintype.card V≤bipartiteNum G+2 := by
    have sz := card_sdiff_add_card_eq_card (subset_univ ({a,b}:Finset V))
    rw [card_univ,card_pair ne] at sz
    have cap := size_bip G bi
    change (univ\{a,b}).card≤bipartiteNum G at cap;omega
  have budget := rank_allowance G gc hn rk r p A ai
  refine ⟨by omega,?_⟩
  by_contra! small;exact bad (protected_bip G gc hn (bip_of_short G hn small) r p A ai)

theorem conflict_failure (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A X : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (c d : V→Bool) (proper : ProperOn G (univ\X) c) :
    let K := A∩insert r (parity G r p)
    allowance G r p A<(X\K).card+(conflicts G (univ\X) (X∩K) c d).card := by
  intro K
  have ind : Indep G K := fun x xm y ym => ai x (mem_inter.mp xm).1 y (mem_inter.mp ym).1
  obtain ⟨Z,bi,incl,sz⟩ := repair G X K ind c d proper
  by_contra! pay
  exact bad ((protected_iff G gc hn r p A ai).mpr ⟨Z,bi,incl,sz.trans pay⟩)

#print axioms repair
#print axioms budget_two
#print axioms conflict_failure
end Minimal180.PairRepair
