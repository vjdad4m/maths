import TriangleCut180
import TriangleReserve180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def FirstForm (J : SimpleGraph V) (U : Finset V) (u v w : V) : Prop :=
  ∃ C⊆U, w∈C ∧ C.card=weightedLeaves J U+1 ∧
    TwoSides J (univ\C) u v ∧ ∀ x∈C, Dominates J (univ\C) x

theorem eligible_mono (J : SimpleGraph V) {X Y : Finset V} (sub : X⊆Y) :
    weightedLeaves J X≤weightedLeaves J Y := by
  classical
  apply Finset.sup_le
  intro T h
  exact (card_le_card (inter_subset_inter sub (Subset.rfl : leaves T⊆leaves T))).trans
    (le_sup (f:=fun K => (Y∩leaves K).card) h)

private theorem sides_score (J : SimpleGraph V) (u v : V) (uv : u≠v)
    (C W : Finset V) (cw : C⊆W) (s : TwoSides J (univ\C) u v)
    (dom : ∀ x∈C, Dominates J (univ\C) x) :
    C.card≤weightedLeaves (J⊔SimpleGraph.edge u v) W := by
  classical
  let G := J⊔SimpleGraph.edge u v
  let D := univ\C
  obtain ⟨ud,vd,_,cuts⟩ := s
  have edge : G.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩)
  have core : Con G D := (connected_cuts G D).mpr ⟨⟨u,ud⟩,fun f good =>
    cuts f (fun x hx y hy e => good x hx y hy (Or.inl e)) (good u ud v vd edge)⟩
  have upper := weightedCore G D W core (fun x h => by
    obtain ⟨y,yd,e⟩ := dom x (by simpa [D] using h)
    exact ⟨y,yd,Or.inl e⟩)
  exact (card_le_card (show C⊆W\D from fun x hx => mem_sdiff.mpr ⟨cw hx,by simp [D,hx]⟩)).trans upper

/-- The two-component certificate exists exactly when the best upper tree
still beats the original lower optimum after erasing both endpoint weights. -/
theorem first_iff_erased_gain (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v) (U : Finset V) :
    FirstForm J U u v w ↔ weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge u v) (U\{u,v}) := by
  classical
  let W := U\{u,v}
  let G := J⊔SimpleGraph.edge u v
  constructor
  · rintro ⟨C,cu,_,size,s,dom⟩
    have un : u∉C := (mem_sdiff.mp s.1).2
    have vn : v∉C := (mem_sdiff.mp s.2.1).2
    have cw : C⊆W := by
      intro x hx; apply mem_sdiff.mpr; refine ⟨cu hx,?_⟩
      rintro h
      rcases (show x=u ∨ x=v by simpa using h) with rfl|rfl
      · exact un hx
      · exact vn hx
    have := sides_score J u v uv C W cw s dom
    change weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge u v) W
    omega
  · intro high
    have lower := eligible_mono J (show W⊆U from sdiff_subset)
    have gain : weightedLeaves J W<weightedLeaves G W := lower.trans_lt high
    obtain ⟨T,sub,tr,opt⟩ := tree_opt G (jc.mono le_sup_left) W
    have win : weightedLeaves J W<(W∩leaves T).card := opt ▸ gain
    obtain ⟨_,_,S,_,_,best,out,eq,_⟩ := common_neighbor_rotation J T (by omega) u v w uv old uw wv W sub tr win
    have one := congrArg card eq
    rw [card_insert_of_not_mem out,best,opt] at one
    have same : weightedLeaves J W=weightedLeaves J U := by change weightedLeaves J U<weightedLeaves G W at high; omega
    obtain ⟨C,cw,mid,size,s|s|s⟩ := (triangle_gain_iff_core J jc hn u v w uv old uw wv W).mp gain
    · exact ⟨C,cw.trans sdiff_subset,mid,same ▸ size,s⟩
    · exact ((mem_sdiff.mp (cw s.1)).2 (mem_insert_self ..)).elim
    · exact ((mem_sdiff.mp (cw s.1)).2 (mem_insert_of_mem (mem_singleton_self _))).elim

/-- A gain has the first form whenever each eligible endpoint has an old
neighbor outside the eligibility set. Such a tip can never lack domination. -/
theorem first_of_supported_tips (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v)
    (U : Finset V) (support : ∀ x∈({u,v}:Finset V), x∈U → ∃ y∉U, J.Adj x y)
    (gain : weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge u v) U) :
    FirstForm J U u v w := by
  obtain ⟨C,cu,mid,size,cert⟩ := (triangle_gain_iff_core J jc hn u v w uv old uw wv U).mp gain
  have no {x y} (xt : x∈({u,v}:Finset V)) (block : NeedsTip J C (univ\C) x y) : False := by
    obtain ⟨z,out,e⟩ := support x xt (cu block.1)
    exact block.2.2.2.1 ⟨z,mem_sdiff.mpr ⟨mem_univ _,fun h => out (cu h)⟩,e⟩
  rcases cert with s|s|s
  · exact ⟨C,cu,mid,size,s⟩
  · exact (no (mem_insert_self ..) s).elim
  · exact (no (mem_insert_of_mem (mem_singleton_self _)) s).elim

/-- A lower optimum with a degree-two eligible middle and no eligible
endpoint leaf yields the first form, since rotating can gain with both
endpoint weights erased. -/
theorem first_of_tree (J T : SimpleGraph V) [DecidableRel T.Adj] (hn : 3<Fintype.card V)
    (u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (tr : T.IsTree) (sub : T≤J)
    (U : Finset V) (opt : (U∩leaves T).card=weightedLeaves J U)
    (uw : T.Adj u w) (vw : T.Adj v w) (elig : w∈U) (two : T.degree w≤2)
    (avoid : ∀ x∈({u,v}:Finset V), x∈U → x∉leaves T) : FirstForm J U u v w := by
  classical
  let W := U\{u,v}
  have eq : W∩leaves T=U∩leaves T := by
    ext x; constructor
    · exact fun h => mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp h).1).1,(mem_inter.mp h).2⟩
    · intro h; obtain ⟨a,b⟩ := mem_inter.mp h
      exact mem_inter.mpr ⟨mem_sdiff.mpr ⟨a,fun k => avoid x k a b⟩,b⟩
  have lo := score_of_tree J T sub tr W
  rw [eq,opt] at lo
  have kept := le_antisymm (eligible_mono J (show W⊆U from sdiff_subset)) lo
  have ow : (W∩leaves T).card=weightedLeaves J W := by rw [eq,opt,kept]
  have wm : w∈W := mem_sdiff.mpr ⟨elig,by simp [uw.ne.symm,vw.ne.symm]⟩
  have gain := optimal_middle_gain J T hn u v w uv tr sub W ow uw vw wm two
  rw [kept] at gain
  exact (first_iff_erased_gain J (tr.isConnected.mono sub) (by omega) u v w uv old (sub uw) (sub vw).symm U).mpr gain

/-- A first-form certificate requires one lower optimum avoiding both eligible
tips simultaneously, even when the tips each admit a different avoiding tree. -/
theorem first_requires_old_avoidance (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v) (U : Finset V)
    (cert : FirstForm J U u v w) :
    ∃ T≤J, T.IsTree ∧ (U∩leaves T).card=weightedLeaves J U ∧
      ∀ z∈({u,v}:Finset V), z∈U → z∉leaves T := by
  classical
  let W := U\{u,v}
  let G := J⊔SimpleGraph.edge u v
  have gain : weightedLeaves J U<weightedLeaves G W :=
    (first_iff_erased_gain J jc hn u v w uv old uw wv U).mp cert
  have lower := eligible_mono J (show W⊆U from sdiff_subset)
  obtain ⟨S,sg,st,optS⟩ := tree_opt G (jc.mono le_sup_left) W
  have win : weightedLeaves J W<(W∩leaves S).card := optS ▸ (lower.trans_lt gain)
  obtain ⟨_,_,_,_,_,best,out,eq,_⟩ := common_neighbor_rotation J S (by omega) u v w uv old uw wv W sg st win
  have one := congrArg card eq
  rw [card_insert_of_not_mem out,best,optS] at one
  obtain ⟨T,sub,tr,opt⟩ := tree_opt J jc W
  have bound := score_of_tree J T sub tr U
  have contain : W∩leaves T⊆U∩leaves T := inter_subset_inter sdiff_subset Subset.rfl
  have count := card_le_card contain
  have same : W∩leaves T=U∩leaves T := eq_of_subset_of_card_le contain (by omega)
  refine ⟨T,sub,tr,by omega,?_⟩
  intro z zt zu lf
  have inside : z∈W∩leaves T := same ▸ mem_inter.mpr ⟨zu,lf⟩
  exact (mem_sdiff.mp (mem_inter.mp inside).1).2 zt

#print axioms first_requires_old_avoidance
#print axioms first_iff_erased_gain
#print axioms first_of_supported_tips
#print axioms first_of_tree
end Minimal180
