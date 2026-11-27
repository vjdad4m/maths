import Plateau180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Removing the new edge from a tree which uses it can be repaired by
one old edge. All original edges of the tree except the new one survive. -/
theorem reconnect (J T : SimpleGraph V) (jc : J.Connected) (tree : T.IsTree)
    (u v : V) (sub : T≤J⊔SimpleGraph.edge u v) (used : T.Adj u v) (absent : ¬J.Adj u v) :
    ∃ S≤J, S.IsTree ∧ T⊓J≤S ∧ ∃ a b, S.Adj a b ∧ ¬T.Adj a b ∧ S≤T⊔SimpleGraph.edge a b := by
  classical
  obtain ⟨S,sj,st,ret⟩ := keep_target J T jc tree
  have keep : T⊓J≤S := fun _ _ h => ret ⟨h.2,h.1⟩
  have missing : T.edgeFinset \ S.edgeFinset={s(u,v)} := by
    ext z
    induction z using Sym2.ind with
    | _ x y =>
      simp only [mem_sdiff,mem_edgeFinset,mem_singleton]
      constructor
      · rintro ⟨t,s⟩
        rcases sub t with j|e
        · exact (s (keep ⟨t,j⟩)).elim
        · exact ((adj_edge ..).mp e).1.symm
      · intro eq
        rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨used,fun e => absent (sj e)⟩
        · exact ⟨used.symm,fun e => absent (sj e).symm⟩
  have count := card_sdiff_add_card_inter T.edgeFinset S.edgeFinset
  rw [missing,card_singleton,inter_comm] at count
  have rev := card_sdiff_add_card_inter S.edgeFinset T.edgeFinset
  have one : (S.edgeFinset \ T.edgeFinset).card=1 := by
    have := tree.card_edgeFinset; have := st.card_edgeFinset; omega
  obtain ⟨z,only⟩ := card_eq_one.mp one
  induction z using Sym2.ind with
  | _ a b =>
    have edge : s(a,b)∈S.edgeFinset \ T.edgeFinset := by rw [only]; simp
    obtain ⟨sa,ta⟩ := mem_sdiff.mp edge
    refine ⟨S,sj,st,keep,a,b,mem_edgeFinset.mp sa,fun h => ta (mem_edgeFinset.mpr h),?_⟩
    intro x y e
    by_cases old : T.Adj x y
    · exact Or.inl old
    have fresh : s(x,y)∈S.edgeFinset \ T.edgeFinset := mem_sdiff.mpr ⟨mem_edgeFinset.mpr e,fun h => old (mem_edgeFinset.mp h)⟩
    rw [only,mem_singleton] at fresh
    exact Or.inr ((adj_edge ..).mpr ⟨fresh.symm,e.ne⟩)

omit [Fintype V] [DecidableEq V] in
private theorem old_edge_only (J T : SimpleGraph V) (u v : V)
    (sub : T≤J⊔SimpleGraph.edge u v) (no : ¬T.Adj u v) : T≤J := by
  intro x y xy
  rcases sub xy with h|h
  · exact h
  · rcases ((edge_adj ..).mp h).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (no xy).elim
    · exact (no xy.symm).elim

omit [DecidableEq V] in
private theorem survives (T S : SimpleGraph V) (sc : S.Connected) (hn : 1<Fintype.card V)
    (a b : V) (sub : S≤T⊔SimpleGraph.edge a b) {w : V} (leaf : w∈leaves T)
    (wa : w≠a) (wb : w≠b) : w∈leaves S := by
  have old {q} (e : S.Adj w q) : T.Adj w q := by
    rcases sub e with h|h
    · exact h
    · rcases ((edge_adj ..).mp h).1 with h|h
      · exact (wa h.1).elim
      · exact (wb h.1).elim
  exact leaf_of_unique S sc hn w (fun e f => leaf_unique T leaf (old e) (old f))

/-- One edge can raise the maximum eligible-leaf score by at most two. -/
theorem gain_cap (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (absent : ¬J.Adj u v) (U : Finset V) :
    weightedLeaves (J⊔SimpleGraph.edge u v) U≤weightedLeaves J U+2 := by
  classical
  obtain ⟨T,sub,tr,opt⟩ := tree_opt (J⊔SimpleGraph.edge u v) (jc.mono le_sup_left) U
  by_cases used : T.Adj u v
  · obtain ⟨S,sj,st,_,a,b,ab,_,ss⟩ := reconnect J T jc tr u v sub used absent
    have bound : U ∩ leaves T ⊆ (U ∩ leaves S) ∪ {a,b} := by
      intro x hx
      by_cases h : x∈({a,b}:Finset V)
      · exact mem_union_right _ h
      have n : x≠a ∧ x≠b := by simpa using h
      exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hx).1,survives T S st.isConnected hn a b ss (mem_inter.mp hx).2 n.1 n.2⟩)
    have score : (U ∩ leaves S).card≤weightedLeaves J U :=
      le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,sj,st⟩)
    have count := (card_le_card bound).trans (card_union_le ..)
    rw [card_pair ab.ne,opt] at count
    omega
  · have score : (U ∩ leaves T).card≤weightedLeaves J U :=
      le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,old_edge_only J T u v sub used,tr⟩)
    omega

/-- If one edge raises the optimum by two, a lower optimum can reach an
upper optimum in a single exchange and retain all its old eligible leaves.
The edge removed by this exchange can be internal to the fundamental path. -/
theorem double_gain_exchange (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (absent : ¬J.Adj u v) (U : Finset V)
    (jump : weightedLeaves (J⊔SimpleGraph.edge u v) U=weightedLeaves J U+2) :
    ∃ S≤J, S.IsTree ∧ (U ∩ leaves S).card=weightedLeaves J U ∧
    ∃ T≤S⊔SimpleGraph.edge u v, T.IsTree ∧ (U ∩ leaves T).card=weightedLeaves (J⊔SimpleGraph.edge u v) U ∧
      U ∩ leaves S ⊆ U ∩ leaves T ∧ T.Adj u v ∧
      ∃ a b, S.Adj a b ∧ ¬T.Adj a b ∧ S≤T⊔SimpleGraph.edge a b := by
  classical
  obtain ⟨T,sub,tr,opt⟩ := tree_opt (J⊔SimpleGraph.edge u v) (jc.mono le_sup_left) U
  have used : T.Adj u v := by
    apply Classical.byContradiction
    intro no
    have low : (U ∩ leaves T).card≤weightedLeaves J U :=
      le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,old_edge_only J T u v sub no,tr⟩)
    omega
  obtain ⟨S,sj,st,kept,a,b,ab,miss,ss⟩ := reconnect J T jc tr u v sub used absent
  let C := U ∩ leaves S
  let B := U ∩ leaves T
  have cover : B ⊆ C ∪ {a,b} := by
    intro x hx
    by_cases h : x∈({a,b}:Finset V)
    · exact mem_union_right _ h
    have n : x≠a ∧ x≠b := by simpa using h
    exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hx).1,survives T S st.isConnected hn a b ss (mem_inter.mp hx).2 n.1 n.2⟩)
  have cap : C.card≤weightedLeaves J U :=
    le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,sj,st⟩)
  have bound := card_union_le C ({a,b}:Finset V)
  rw [card_pair ab.ne] at bound
  have lo := card_le_card cover
  change B.card=_ at opt
  have eq := eq_of_subset_of_card_le cover (by omega)
  refine ⟨S,sj,st,by change C.card=_; omega,T,?_,tr,opt,?_,used,a,b,ab,miss,ss⟩
  · intro x y e
    rcases sub e with j|f
    · exact Or.inl (kept ⟨e,j⟩)
    · exact Or.inr f
  · change C⊆B
    rw [eq]
    exact subset_union_left

/-- Joining two eligible pendant vertices cannot improve the weighted
leaf maximum. Their two restored leaves pay for all reconnection losses. -/
theorem pendant_pair_no_gain (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (absent : ¬J.Adj u v) (U : Finset V) (um : u∈U) (vm : v∈U)
    (ul : u∈leaves J) (vl : v∈leaves J) :
    weightedLeaves (J⊔SimpleGraph.edge u v) U=weightedLeaves J U := by
  classical
  apply le_antisymm _ (leaf_mono _ le_sup_left _)
  obtain ⟨T,sub,tr,opt⟩ := tree_opt (J⊔SimpleGraph.edge u v) (jc.mono le_sup_left) U
  by_cases used : T.Adj u v
  · obtain ⟨S,sj,st,_,a,b,ab,_,ss⟩ := reconnect J T jc tr u v sub used absent
    let B := U ∩ leaves T
    let C := U ∩ leaves S
    let F := ({a,b} : Finset V)
    let E := ({u,v} : Finset V)
    have oldc {w} (wE : w∈E) : w∈C := by
      rcases (show w=u ∨ w=v by simpa [E] using wE) with rfl|rfl
      · exact mem_inter.mpr ⟨um,leaf_of_unique S st.isConnected hn _ (fun x y => leaf_unique J ul (sj x) (sj y))⟩
      · exact mem_inter.mpr ⟨vm,leaf_of_unique S st.isConnected hn _ (fun x y => leaf_unique J vl (sj x) (sj y))⟩
    have lost : B \ C ⊆ F \ E := by
      intro w hw
      obtain ⟨wb,no⟩ := mem_sdiff.mp hw
      refine mem_sdiff.mpr ⟨?_,fun h => no (oldc h)⟩
      apply Classical.byContradiction
      intro n
      have ne : w≠a ∧ w≠b := by simpa [F] using n
      exact no (mem_inter.mpr ⟨(mem_inter.mp wb).1,survives T S st.isConnected hn a b ss (mem_inter.mp wb).2 ne.1 ne.2⟩)
    have gained : E \ F ⊆ C \ B := by
      intro w hw
      obtain ⟨we,wf⟩ := mem_sdiff.mp hw
      refine mem_sdiff.mpr ⟨oldc we,?_⟩
      intro wb
      obtain ⟨i,wi⟩ := exists_adj S st.isConnected hn w
      have wiT : T.Adj w i := by
        rcases ss wi with e|e
        · exact e
        · rcases ((edge_adj ..).mp e).1 with e|e
          · exact (wf (e.1 ▸ mem_insert_self _ _)).elim
          · exact (wf (e.1 ▸ mem_insert_of_mem (mem_singleton_self _))).elim
      rcases (show w=u ∨ w=v by simpa [E] using we) with rfl|rfl
      · exact absent ((leaf_unique T (mem_inter.mp wb).2 wiT used) ▸ sj wi)
      · exact absent (((leaf_unique T (mem_inter.mp wb).2 wiT used.symm) ▸ sj wi).symm)
    have fCount : F.card=2 := card_pair ab.ne
    have eCount : E.card=2 := card_pair used.ne
    have first := card_sdiff_add_card_inter F E
    have second := card_sdiff_add_card_inter E F
    rw [inter_comm] at second
    have lc := card_le_card lost
    have gc := card_le_card gained
    have bc := card_sdiff_add_card_inter B C
    have cb := card_sdiff_add_card_inter C B
    rw [inter_comm] at cb
    have score : C.card≤weightedLeaves J U :=
      le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,sj,st⟩)
    change B.card=_ at opt
    omega
  · exact opt ▸ (le_sup (f:=fun K => (U ∩ leaves K).card) (mem_filter.mpr ⟨mem_univ _,old_edge_only J T u v sub used,tr⟩))

/-- In a tight lower graph with two eligible pendant endpoints, a rank
drop on adding a within-layer edge would already give a counterexample
to the original unrooted conjecture, using the certified gadget. -/
theorem pendant_pair_counter (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (r u v : V) (odd : Bool) (A : Finset V) (absent : ¬J.Adj u v) (flat : J.dist u r=J.dist v r)
    (ul : u∈leaves J) (vl : v∈leaves J) (ai : Indep (J⊔SimpleGraph.edge u v) A)
    (um : u∈eligible A (parity J r odd) r) (vm : v∈eligible A (parity J r odd) r)
    (rank : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
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
      obtain ⟨p,e,d⟩ := Graffiti169.exists_predecessor J jc r x ne
      exact ⟨p,Or.inl e,d⟩
  have pe : parity H r odd=parity J r odd := by ext x; simp only [mem_parity,dist.2 x]
  apply of_failed_local H dist.1 hn r odd
  intro all
  have valid := all A ai
  rw [pe] at valid
  have same := pendant_pair_no_gain J jc hn u v absent (eligible A (parity J r odd) r) um vm ul vl
  change weightedLeaves H _=weightedLeaves J _ at same
  change bipartiteNum J=bipartiteNum H+1 at rank
  omega

/-- A concrete one-arm case with a degree-two parent and a free receiving
endpoint. Every optimal tree of the lower graph has the necessary
attachment because the old tip is pendant. -/
theorem pendant_rotation (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (u v p s : V) (uv : u≠v) (up : u≠p) (vl : v∈leaves J) (vp : J.Adj v p)
    (vs : v≠s) (two : ∀ x, J.Adj p x → x=v ∨ x=s)
    (U : Finset V) (pm : p∈U) (free : u∉U) :
    weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge u v) U := by
  classical
  obtain ⟨T,sub,tr,opt⟩ := tree_opt J jc U
  have leaf : v∈leaves T := leaf_of_unique T tr.isConnected (by omega) v (fun a b => leaf_unique J vl (sub a) (sub b))
  obtain ⟨q,vq⟩ := exists_adj T tr.isConnected (by omega) v
  have pv := ((leaf_unique J vl (sub vq) vp) ▸ vq).symm
  have pts : T.Adj p s := by
    apply Classical.byContradiction
    intro no
    have only {z} (e : T.Adj p z) : z=v := (two z (sub e)).resolve_right (fun k => no (k ▸ e))
    exact leaves_nonadjacent T tr hn pv (leaf_of_unique T tr.isConnected (by omega) p
      (fun e f => (only e).trans (only f).symm)) leaf
  have side := leaf_side T tr pv.symm leaf uv
  rw [Sym2.eq_swap] at side
  exact rotation_gain _ (by omega) J T le_sup_left sub tr U opt u v p s
    (Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩)) up pv pts vs (fun _ e => two _ (sub e))
    pm (fun h => free (mem_inter.mp h).1) side

#print axioms pendant_pair_counter
#print axioms pendant_rotation
#print axioms reconnect
#print axioms gain_cap
#print axioms double_gain_exchange
#print axioms pendant_pair_no_gain
end Minimal180
