import Reconnect180
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def interior {J : SimpleGraph V} {u v : V} (p : J.Walk u v) : Finset V :=
  (p.support.toFinset.erase u).erase v

/-- Replace a restored edge by any simple old path. Only upper-tree leaves strictly
inside that path can be lost. Every old edge of the upper tree is retained. -/
theorem bypass_repair (J T : SimpleGraph V) (hn : 1<Fintype.card V) (u v : V)
    (uv : u≠v) (tr : T.IsTree) (sub : T≤J⊔SimpleGraph.edge u v) (used : T.Adj u v)
    (p : J.Walk u v) (hp : p.IsPath) :
    ∃ S≤J, S.IsTree ∧ T⊓J≤S ∧ S≤(T⊓J)⊔p.toSubgraph.spanningCoe ∧ leaves T\interior p⊆leaves S := by
  classical
  let H := (T⊓J)⊔p.toSubgraph.spanningCoe
  let lift : p.toSubgraph.coe →g H :=
    { toFun := fun x => x.1
      map_rel' := fun e => Or.inr e }
  have route : H.Reachable u v :=
    (p.toSubgraph_connected ⟨u,p.start_mem_verts_toSubgraph⟩ ⟨v,p.end_mem_verts_toSubgraph⟩).map lift
  have step {a b : V} (e : T.Adj a b) : H.Reachable a b := by
    rcases sub e with old|added
    · exact (show H.Adj a b from Or.inl ⟨e,old⟩).reachable
    · rcases ((edge_adj ..).mp added).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact route
      · exact route.symm
  have conn : H.Connected := by
    letI : Nonempty V := ⟨u⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨w⟩ := tr.isConnected a b
    induction w with
    | nil => exact .refl _
    | cons e _ ih => exact (step e).trans ih
  obtain ⟨S,sh,st,keep⟩ := keep_target H T conn tr
  have hj : H≤J := sup_le inf_le_right (fun _ _ e => p.toSubgraph.adj_sub e)
  refine ⟨S,sh.trans hj,st,fun _ _ h => keep ⟨Or.inl h,h.1⟩,sh,?_⟩
  intro x hx
  obtain ⟨lf,out⟩ := mem_sdiff.mp hx
  by_cases present : J.Adj u v
  · have tj : T≤J := sub.trans (sup_le le_rfl (by rw [← sup_eq_left]; exact sup_edge_of_adj J present))
    have incl : T≤S := fun _ _ e => keep ⟨Or.inl ⟨e,tj e⟩,e⟩
    have eq := eq_of_subset_of_card_le (edgeFinset_mono incl)
      (by have := tr.card_edgeFinset; have := st.card_edgeFinset; omega)
    exact edgeFinset_inj.mp eq ▸ lf
  have nn := Walk.not_nil_of_ne (p:=p) uv
  apply leaf_of_unique S st.isConnected hn x
  by_cases xu : x=u
  · subst x
    have only {y} (e : S.Adj u y) : y=p.snd := by
      rcases sh e with old|path
      · have yv := leaf_unique T lf old.1 used
        exact (present (yv ▸ old.2)).elim
      · have n : y∈p.toSubgraph.neighborSet u := path
        rwa [hp.neighborSet_toSubgraph_startpoint nn,Set.mem_singleton_iff] at n
    exact fun e f => (only e).trans (only f).symm
  by_cases xv : x=v
  · subst x
    have only {y} (e : S.Adj v y) : y=p.penultimate := by
      rcases sh e with old|path
      · have yu := leaf_unique T lf old.1 used.symm
        exact (present (yu ▸ old.2).symm).elim
      · have n : y∈p.toSubgraph.neighborSet v := path
        rwa [hp.neighborSet_toSubgraph_endpoint nn,Set.mem_singleton_iff] at n
    exact fun e f => (only e).trans (only f).symm
  have old {y} (e : S.Adj x y) : T.Adj x y := by
    rcases sh e with h|h
    · exact h.1
    · exact (out (by simp [interior,xu,xv,Walk.mem_support_of_adj_toSubgraph h])).elim
  exact fun e f => leaf_unique T lf (old e) (old f)

/-- The gain from a chord cannot exceed the eligible leaves of an optimal
upper tree strictly inside any lower-graph path between the endpoints. -/
theorem path_gain_bound (J : SimpleGraph V) (hn : 1<Fintype.card V) (u v : V) (uv : u≠v)
    (U : Finset V) (p : J.Walk u v) (hp : p.IsPath)
    (T : SimpleGraph V) (sub : T≤J⊔SimpleGraph.edge u v) (tr : T.IsTree) :
    (U∩leaves T).card ≤ weightedLeaves J U+((U∩leaves T)∩interior p).card := by
  classical
  by_cases used : T.Adj u v
  · obtain ⟨S,sj,st,_,_,repair⟩ := bypass_repair J T hn u v uv tr sub used p hp
    have incl : (U∩leaves T)\interior p ⊆ U∩leaves S := by
      intro x hx
      obtain ⟨h,o⟩ := mem_sdiff.mp hx
      obtain ⟨a,b⟩ := mem_inter.mp h
      exact mem_inter.mpr ⟨a,repair (mem_sdiff.mpr ⟨b,o⟩)⟩
    have sc : (U∩leaves S).card≤weightedLeaves J U := le_sup (f:=fun K => (U∩leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,sj,st⟩)
    have bound := (card_le_card incl).trans sc
    have sum := card_sdiff_add_card_inter (U∩leaves T) (interior p)
    omega
  · have tj : T≤J := by
      intro x y xy
      rcases sub xy with h|h
      · exact h
      · rcases ((edge_adj ..).mp h).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (used xy).elim
        · exact (used xy.symm).elim
    exact (le_sup (f:=fun K => (U∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,tj,tr⟩)).trans (Nat.le_add_right ..)

/-- An old path whose strict interior is ineligible makes a chord score-neutral. -/
theorem bypass_no_gain (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (uv : u≠v) (U : Finset V) (p : J.Walk u v) (hp : p.IsPath)
    (free : Disjoint U (interior p)) :
    weightedLeaves (J⊔SimpleGraph.edge u v) U=weightedLeaves J U := by
  classical
  obtain ⟨T,sub,tr,opt⟩ := tree_opt _ (jc.mono (show J≤J⊔SimpleGraph.edge u v from le_sup_left)) U
  have bound := path_gain_bound J hn u v uv U p hp T sub tr
  have d : Disjoint (U∩leaves T) (interior p) := free.mono_left inter_subset_left
  rw [disjoint_iff_inter_eq_empty.mp d,card_empty,Nat.add_zero,opt] at bound
  exact le_antisymm bound (leaf_mono _ le_sup_left _)

/-- A flat chord with an ineligible bypass, a rank drop, and a tight lower
state would give a genuine finite connected counterexample to #180. -/
theorem bypass_counter (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (r u v : V) (uv : u≠v) (level : J.dist u r=J.dist v r)
    (odd : Bool) (A : Finset V) (ai : Indep (J⊔SimpleGraph.edge u v) A)
    (p : J.Walk u v) (hp : p.IsPath) (free : Disjoint (eligible A (parity J r odd) r) (interior p))
    (rank : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  let H := J⊔SimpleGraph.edge u v
  have dist : H.Connected ∧ ∀ x, H.dist x r=J.dist x r := by
    apply layers H r (fun x => J.dist x r) J.dist_self
    · intro x y e
      rcases e with j|h
      · have d := jc.dist_triangle (u:=x) (v:=y) (w:=r)
        rw [dist_eq_one_iff_adj.mpr j] at d
        omega
      · rcases ((edge_adj ..).mp h).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
    · intro x ne
      obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor J jc r x ne
      exact ⟨w,Or.inl e,d⟩
  have pe : parity H r odd=parity J r odd := by ext x; simp only [mem_parity,dist.2 x]
  apply of_failed_local H dist.1 hn r odd
  intro all
  have valid := all A ai
  rw [pe] at valid
  have same := bypass_no_gain J jc hn u v uv _ p hp free
  change weightedLeaves H _=weightedLeaves J _ at same
  change bipartiteNum J=bipartiteNum H+1 at rank
  omega

#print axioms bypass_counter
#print axioms bypass_repair
#print axioms path_gain_bound
#print axioms bypass_no_gain
end Minimal180
