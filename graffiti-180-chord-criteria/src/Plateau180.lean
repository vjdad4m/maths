import Rotation180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Extend all currently available target-tree edges to a spanning tree.
The minimal connected subgraph argument is the forest extension used in
Strong179. Here the forest is the intersection with a specified tree. -/
theorem keep_target (H K : SimpleGraph V) (hc : H.Connected) (kt : K.IsTree) :
    ∃ S≤H, S.IsTree ∧ H⊓K≤S := by
  classical
  obtain ⟨S,sub,m⟩ := {L : SimpleGraph V | L.Connected ∧ H⊓K≤L}.toFinite.exists_minimal_le
    (show H.Connected ∧ H⊓K≤H from ⟨hc,inf_le_left⟩)
  refine ⟨S,sub,⟨m.prop.1,?_⟩,m.prop.2⟩
  intro v w cycle
  by_cases all : ∀ e∈w.edges, e∈K.edgeSet
  · exact kt.IsAcyclic (w.transfer K all) (cycle.transfer all)
  push_neg at all
  obtain ⟨e,ew,ek⟩ := all
  induction e using Sym2.ind with
  | _ a b =>
    have ns : ¬S.IsBridge s(a,b) := fun h => (isBridge_iff_mem_and_forall_cycle_not_mem.mp h).2 w cycle ew
    have strict : S.deleteEdges {s(a,b)} < S := by
      refine lt_of_le_of_ne (S.deleteEdges_le _) ?_
      intro same
      have n : ¬(S.deleteEdges {s(a,b)}).Adj a b := by simp
      rw [same] at n
      exact n ((mem_edgeSet S).mp (w.edges_subset_edgeSet ew))
    apply m.not_prop_of_lt strict
    refine ⟨m.prop.1.connected_delete_edge_of_not_isBridge ns,?_⟩
    intro i j h
    refine deleteEdges_adj.mpr ⟨m.prop.2 h,?_⟩
    intro e
    exact ek ((Set.mem_singleton_iff.mp e) ▸ (mem_edgeSet K).mpr h.2)

theorem leaves_nonadjacent (T : SimpleGraph V) (tr : T.IsTree) (hn : 2<Fintype.card V)
    {a b : V} (e : T.Adj a b) (la : a∈leaves T) (lb : b∈leaves T) : False := by
  classical
  obtain ⟨k,kn⟩ : ∃ k, k∉({a,b} : Finset V) := by
    by_contra! no
    have h := card_le_card (show univ ⊆ ({a,b}:Finset V) from fun v _ => no v)
    rw [card_univ,card_pair e.ne] at h
    omega
  have ak : a≠k := fun h => kn (h ▸ mem_insert_self _ _)
  have bk : b≠k := fun h => kn (h ▸ mem_insert_of_mem (mem_singleton_self _))
  obtain ⟨i,ai,di⟩ := Graffiti169.exists_predecessor T tr.isConnected k a ak
  obtain ⟨j,bj,dj⟩ := Graffiti169.exists_predecessor T tr.isConnected k b bk
  rw [leaf_unique T la ai e] at di
  rw [leaf_unique T lb bj e.symm] at dj
  omega

/-- Moving a leaf to another parent leaves the remaining vertices connected. -/
theorem leaf_side (T : SimpleGraph V) (tr : T.IsTree) {x p v : V}
    (xp : T.Adj x p) (xl : x∈leaves T) (vx : v≠x) :
    (T.deleteEdges {s(x,p)}).Reachable p v := by
  classical
  let f (w : V) := if w=x then p else w
  let J := T.deleteEdges {s(x,p)}
  have project {a b} (walk : T.Walk a b) : J.Reachable (f a) (f b) := by
    induction walk with
    | nil => exact Reachable.refl _
    | @cons a c b e _ ih =>
      by_cases ax : a=x
      · subst a
        have cp := leaf_unique T xl e xp
        have same : f x=f c := by simp [f,cp,xp.ne.symm]
        exact same ▸ ih
      by_cases cx : c=x
      · subst c
        have ap := leaf_unique T xl e.symm xp
        have same : f a=f x := by simp [f,ap,xp.ne.symm]
        exact same ▸ ih
      have kept : J.Adj a c := deleteEdges_adj.mpr ⟨e,by simp [Sym2.eq_iff,ax,cx]⟩
      have ef : J.Adj (f a) (f c) := by simpa only [f,if_neg ax,if_neg cx] using kept
      exact ef.reachable.trans ih
  obtain ⟨walk⟩ := tr.isConnected p v
  simpa [f,xp.ne.symm,vx,J] using project walk

/-- Find a connected carrier for a single target edge, with all protected
leaves having unique neighbors. Every already shared tree edge survives. -/
private theorem carrier (T K : SimpleGraph V) (tr : T.IsTree) (kt : K.IsTree)
    (hn : 2<Fintype.card V) (X : Finset V) (xt : X⊆leaves T) (xk : X⊆leaves K)
    (a b : V) (e : K.Adj a b) (miss : ¬T.Adj a b) :
    ∃ H, H.Connected ∧ H≤T⊔SimpleGraph.edge a b ∧ T⊓K≤H ∧ H.Adj a b ∧
      ∀ x∈X, ∀ i j, H.Adj x i → H.Adj x j → i=j := by
  classical
  have leaf_case {u v : V} (uv : K.Adj u v) (no : ¬T.Adj u v) (xu : u∈X) :
      ∃ H, H.Connected ∧ H≤T⊔SimpleGraph.edge u v ∧ T⊓K≤H ∧ H.Adj u v ∧
        ∀ x∈X, ∀ i j, H.Adj x i → H.Adj x j → i=j := by
    obtain ⟨p,up⟩ := exists_adj T tr.isConnected (by omega) u
    have vp : v≠p := fun h => no (h ▸ up)
    have xv : v∉X := fun h => leaves_nonadjacent K kt hn uv (xk xu) (xk h)
    let D := T.deleteEdges {s(u,p)}
    let H := D⊔SimpleGraph.edge u v
    have add : H.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv.ne⟩)
    have route : H.Reachable u p := add.reachable.trans ((leaf_side T tr up (xt xu) uv.ne.symm).mono (show D≤H from le_sup_left)).symm
    have conn : H.Connected := by
      letI : Nonempty V := ⟨u⟩
      refine ⟨fun i j => ?_⟩
      obtain ⟨walk⟩ := tr.isConnected i j
      induction walk with
      | nil => exact Reachable.refl _
      | @cons i w j iw _ ih =>
        by_cases same : s(i,w)=s(u,p)
        · rcases Sym2.eq_iff.mp same with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact route.trans ih
          · exact route.symm.trans ih
        · exact (show H.Adj i w from Or.inl (deleteEdges_adj.mpr ⟨iw,same⟩)).reachable.trans ih
    refine ⟨H,conn,sup_le_sup_right (T.deleteEdges_le _) _,?_,add,?_⟩
    · intro i j ij
      refine Or.inl (deleteEdges_adj.mpr ⟨ij.1,?_⟩)
      intro same
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp same) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact vp (leaf_unique K (xk xu) uv ij.2)
      · exact vp (leaf_unique K (xk xu) uv ij.2.symm)
    · intro x hx i j hi hj
      by_cases eq : x=u
      · subst x
        have only {w} (h : H.Adj u w) : w=v := by
          rcases h with h|h
          · have info := deleteEdges_adj.mp h
            have wp := leaf_unique T (xt xu) info.1 up
            exact (info.2 (wp ▸ rfl)).elim
          · rcases ((edge_adj ..).mp h).1 with h|h
            · exact h.2
            · exact (uv.ne h.1).elim
        exact (only hi).trans (only hj).symm
      · have original {w} (h : H.Adj x w) : T.Adj x w := by
          rcases h with h|h
          · exact (T.deleteEdges_le _) h
          · rcases ((edge_adj ..).mp h).1 with h|h
            · exact (eq h.1).elim
            · exact (xv (h.1 ▸ hx)).elim
        exact leaf_unique T (xt hx) (original hi) (original hj)
  by_cases ax : a∈X
  · exact leaf_case e miss ax
  by_cases bx : b∈X
  · obtain ⟨H,c,s,sub,ad,pr⟩ := leaf_case e.symm (fun k => miss k.symm) bx
    rw [edge_comm] at s
    exact ⟨H,c,s,sub,ad.symm,pr⟩
  let H := T⊔SimpleGraph.edge a b
  refine ⟨H,tr.isConnected.mono le_sup_left,le_rfl,inf_le_left.trans le_sup_left,
    Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,e.ne⟩),?_⟩
  intro x hx i j hi hj
  have old {w} (h : H.Adj x w) : T.Adj x w := by
    rcases h with h|h
    · exact h
    · rcases ((edge_adj ..).mp h).1 with h|h
      · exact (ax (h.1 ▸ hx)).elim
      · exact (bx (h.1 ▸ hx)).elim
  exact leaf_unique T (xt hx) (old hi) (old hj)

noncomputable def agreement (T K : SimpleGraph V) : ℕ := by
  classical exact (T.edgeFinset ∩ K.edgeFinset).card

/-- One tree-edge exchange retaining the prescribed leaves and increasing
the number of edges in common with the target. -/
def Toward (G K : SimpleGraph V) (X : Finset V) (T S : SimpleGraph V) : Prop :=
  S≤G ∧ S.IsTree ∧ X⊆leaves S ∧ agreement T K<agreement S K ∧
    ∃ a b, ¬T.Adj a b ∧ S.Adj a b ∧ S≤T⊔SimpleGraph.edge a b

theorem protected_step (G T K : SimpleGraph V) (hn : 2<Fintype.card V)
    (tg : T≤G) (kg : K≤G) (tr : T.IsTree) (kt : K.IsTree) (ne : T≠K)
    (X : Finset V) (xt : X⊆leaves T) (xk : X⊆leaves K) : ∃ S, Toward G K X T S := by
  classical
  have notsub : ¬K≤T := by
    intro sub
    have eq := eq_of_subset_of_card_le (edgeFinset_mono sub) (by have := tr.card_edgeFinset; have := kt.card_edgeFinset; omega)
    exact ne (edgeFinset_inj.mp eq).symm
  obtain ⟨a,b,e,miss⟩ : ∃ a b, K.Adj a b ∧ ¬T.Adj a b := by
    apply Classical.byContradiction
    intro no
    exact notsub (fun x y k => Classical.byContradiction (fun m => no ⟨x,y,k,m⟩))
  obtain ⟨H,conn,sub,common,add,unique⟩ := carrier T K tr kt hn X xt xk a b e miss
  obtain ⟨S,sh,st,keep⟩ := keep_target H K conn kt
  have hG : H≤G := sub.trans (sup_le tg (by rw [← sup_eq_left]; exact sup_edge_of_adj G (kg e)))
  have se : S.Adj a b := keep ⟨add,e⟩
  have both : T⊓K≤S := fun _ _ h => keep ⟨common h,h.2⟩
  have strict : T.edgeFinset ∩ K.edgeFinset ⊂ S.edgeFinset ∩ K.edgeFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro z hz
      induction z using Sym2.ind with
      | _ i j =>
        obtain ⟨ti,ki⟩ := mem_inter.mp hz
        exact mem_inter.mpr ⟨mem_edgeFinset.mpr (both ⟨mem_edgeFinset.mp ti,mem_edgeFinset.mp ki⟩),ki⟩
    · intro eq
      have ab : s(a,b)∈S.edgeFinset ∩ K.edgeFinset := mem_inter.mpr ⟨mem_edgeFinset.mpr se,mem_edgeFinset.mpr e⟩
      rw [← eq] at ab
      exact miss (mem_edgeFinset.mp (mem_inter.mp ab).1)
  exact ⟨S,sh.trans hG,st,fun x hx => leaf_of_unique S st.isConnected (by omega) x
    (fun f g => unique x hx _ _ (sh f) (sh g)),card_lt_card strict,a,b,miss,se,sh.trans sub⟩

/-- A fixed set of simultaneous leaves can be kept throughout a sequence
of single tree-edge exchanges. Agreement with the target strictly grows. -/
theorem protected_route (G T K : SimpleGraph V) (hn : 2<Fintype.card V)
    (tg : T≤G) (kg : K≤G) (tr : T.IsTree) (kt : K.IsTree)
    (X : Finset V) (xt : X⊆leaves T) (xk : X⊆leaves K) :
    Relation.ReflTransGen (Toward G K X) T K := by
  classical
  let n := Fintype.card V
  induction h : n-agreement T K using Nat.strong_induction_on generalizing T with
  | h m ih =>
    by_cases eq : T=K
    · subst T; exact .refl
    obtain ⟨S,step⟩ := protected_step G T K hn tg kg tr kt eq X xt xk
    have cap : agreement S K ≤ n := (card_le_card inter_subset_right).trans (by have := kt.card_edgeFinset; omega)
    have lt := step.2.2.2.1
    exact (Relation.ReflTransGen.single step).trans
      (ih _ (by omega) S step.1 step.2.1 step.2.2.1 rfl)

#print axioms leaves_nonadjacent
#print axioms leaf_side
#print axioms keep_target
#print axioms protected_step
#print axioms protected_route
end Minimal180
