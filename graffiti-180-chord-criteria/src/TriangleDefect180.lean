import ParityDefect180
import RankSeparator180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every vertex of a block with at least three vertices has two neighbors. -/
theorem block_neighbors (G : SimpleGraph V) (hc : G.Connected) (hn : 2<Fintype.card V)
    (block : NoCut G) (r : V) : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t := by
  classical
  obtain ⟨s,rs⟩ := exists_adj G hc (by omega) r
  obtain ⟨z,out⟩ : ∃ z, z∉({r,s}:Finset V) := by
    by_contra! no
    have h := card_le_card (show univ⊆({r,s}:Finset V) from fun v _ => no v)
    rw [card_univ,card_pair rs.ne] at h
    omega
  have zr : z≠r := fun h => out (h ▸ mem_insert_self _ _)
  have zs : z≠s := fun h => out (h ▸ mem_insert_of_mem (mem_singleton_self _))
  let K := G.induce ({s}ᶜ : Set V)
  let a : ↥({s}ᶜ : Set V) := ⟨r,rs.ne⟩
  let b : ↥({s}ᶜ : Set V) := ⟨z,zs⟩
  obtain ⟨p⟩ := block s a b
  have nz : a≠b := fun h => zr (congrArg Subtype.val h).symm
  have e : K.Adj a p.snd := p.adj_snd (Walk.not_nil_of_ne nz)
  exact ⟨s,p.snd.val,rs,e,fun h => p.snd.property h.symm⟩

noncomputable def alternating (G : SimpleGraph V) (P : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x∈P ↔ y∉P)
  symm _ _ h := ⟨h.1.symm,by have := h.2; tauto⟩
  loopless _ h := h.1.ne rfl

theorem alternating_parity (G : SimpleGraph V) (hc : G.Connected) (r : V) (odd : Bool) :
    (alternating G (parity G r odd)).Connected ∧
    ∀ s, G.Adj r s → (alternating G (parity G r odd)).Adj r s := by
  obtain ⟨T,sub,tr,op⟩ := Graffiti169.exists_parity_tree G hc r
  constructor
  · apply tr.isConnected.mono
    intro v w e
    refine ⟨sub e,?_⟩
    simp only [mem_parity]
    have := op e
    cases odd <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
  · intro s rs
    refine ⟨rs,?_⟩
    simp only [mem_parity,dist_self,dist_eq_one_iff_adj.mpr rs.symm]
    cases odd <;> decide

private theorem constrained_bound (G : SimpleGraph V) (A P : Finset V) :
    markedBip G (A∩P)≤bipartiteNum G := by
  classical
  apply Finset.sup_le
  intro S h
  exact size_bip G (mem_filter.mp h).2.2

/-- For a root with two neighbors, losing at most one vertex to obtain
bipartiteness suffices for the rooted inequality, for every independent set. -/
theorem rank_one_rooted (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (two : ∃ s t, G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (rank : Fintype.card V≤bipartiteNum G+1) (odd : Bool) : localBound G r (parity G r odd) := by
  classical
  intro A ai
  let P := parity G r odd
  by_cases same : A=P
  · have aux := confined_parity G hc hn r odd.toNat A ai (show A⊆P from same.le)
    have cap := constrained_bound G A P
    change 1+A.card+P.card≤weightedLeaves G (eligible A P r)+markedBip G (A∩P) at aux
    exact aux.trans (Nat.add_le_add_left cap _)
  let H := alternating G P
  obtain ⟨con,star⟩ := alternating_parity G hc r odd
  obtain ⟨T,ts,tt⟩ := con.exists_isTree_le
  obtain ⟨K,kh,kt,keep,_⟩ := full_star_exchange H T ts tt hn r
  obtain ⟨s,t,rs,rt,ne⟩ := two
  have internal : r∉leaves K := fun lf => ne (leaf_unique K lf (keep _ (star s rs)) (keep _ (star t rt)))
  have kg : K≤G := fun _ _ e => (kh e).1
  let D := (A∪P)\(A∩P)
  have pos : D.Nonempty := by
    by_contra! h
    apply same
    ext v
    have no : v∉D := fun hv => h ⟨v,hv⟩
    simp only [D,mem_sdiff,mem_union,mem_inter] at no
    tauto
  have f := forest_strict K kt D pos
  have eq := tree_defect K kt hn r internal A P (fun a ha b hb nab ab => ai a ha b hb nab (kg ab))
    (fun e => (kh e).2)
  change Fintype.card V+_+(K.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+_ at eq
  have limit : (eligible A P r∩leaves K).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun T => (eligible A P r∩leaves T).card) (mem_filter.mpr ⟨mem_univ _,kg,kt⟩)
  change 1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G
  omega

/-- Once a chord has dropped bipartite order from the order of the graph
to one below it, lower tightness forces strict leaf gain. -/
theorem bipartite_lower_chord (G J : SimpleGraph V) (hc : G.Connected) (hn : 2<Fintype.card V)
    (block : NoCut G) (r : V) (odd : Bool) (A : Finset V) (ai : Indep G A)
    (full : bipartiteNum J=Fintype.card V) (drop : bipartiteNum J=bipartiteNum G+1)
    (tight : weightedLeaves J (eligible A (parity G r odd) r)+bipartiteNum J=1+A.card+(parity G r odd).card) :
    weightedLeaves J (eligible A (parity G r odd) r)<weightedLeaves G (eligible A (parity G r odd) r) := by
  have bound := rank_one_rooted G hc (by omega) r (block_neighbors G hc hn block r) (by omega) odd A ai
  omega

theorem virtual_tree (r : V) (p : V→V) (d : V→ℕ) (down : ∀ v≠r, d (p v)<d v) :
    ∃ T : SimpleGraph V, T.IsTree ∧ ∀ v≠r, T.Adj v (p v) := by
  classical
  let T : SimpleGraph V :=
    { Adj := fun a b => (a≠r ∧ p a=b) ∨ (b≠r ∧ p b=a)
      symm _ _ h := h.symm
      loopless := by rintro x (⟨ne,h⟩|⟨ne,h⟩) <;> have := down x ne <;> rw [h] at this <;> omega }
  have reach (v : V) : T.Reachable v r := by
    induction h : d v using Nat.strong_induction_on generalizing v with
    | h m ih =>
      by_cases eq : v=r
      · subst v; exact .refl _
      exact (show T.Adj v (p v) from Or.inl ⟨eq,rfl⟩).reachable.trans (ih _ (h ▸ down v eq) _ rfl)
  have conn := (connected_iff_exists_forall_reachable T).mpr ⟨r,fun v => (reach v).symm⟩
  have sub : T.edgeFinset⊆(univ.erase r).image (fun v => s(v,p v)) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rcases (show T.Adj a b from mem_edgeFinset.mp he) with ⟨ne,h⟩|⟨ne,h⟩
      · exact mem_image.mpr ⟨a,mem_erase.mpr ⟨ne,mem_univ _⟩,by rw [h]⟩
      · exact mem_image.mpr ⟨b,mem_erase.mpr ⟨ne,mem_univ _⟩,by rw [h,Sym2.eq_swap]⟩
  have tree : T.IsTree := isTree_iff_connected_and_card.mpr (And.intro conn (le_antisymm (by
    have size := (card_le_card sub).trans card_image_le
    have erase := card_erase_add_one (mem_univ r)
    rw [card_univ] at erase
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
    omega) conn.card_vert_le_card_edgeSet_add_one))
  exact ⟨T,tree,fun _ ne => Or.inl ⟨ne,rfl⟩⟩

/-- A prescribed two-edge path and two root edges extend to one spanning
tree if the root edges avoid the tips. -/
theorem prescribed_spokes (H : SimpleGraph V) (conn : H.Connected) (r u v w s t : V)
    (ur : u≠r) (vr : v≠r) (uw : H.Adj u w) (vw : H.Adj v w)
    (rs : H.Adj r s) (rt : H.Adj r t) (st : s≠t)
    (su : s≠u) (sv : s≠v) (tu : t≠u) (tv : t≠v) :
    ∃ T≤H, T.IsTree ∧ r∉leaves T ∧ T.Adj u w ∧ T.Adj v w := by
  classical
  let tips := ({u,v}:Finset V)
  let p (x:V) := if x∈tips then w else r
  let d (x:V) := if x=r then 0 else if x∈tips then 2 else 1
  have wn : w∉tips := by simp [tips,uw.ne.symm,vw.ne.symm]
  have down (x : V) (ne : x≠r) : d (p x)<d x := by
    by_cases xt : x∈tips
    · by_cases wr : w=r <;> simp [p,d,xt,ne,wr,wn]
    · simp [p,d,xt,ne]
  obtain ⟨K,kt,edges⟩ := virtual_tree r p d down
  obtain ⟨T,sub,tr,keep⟩ := keep_target H K conn kt
  have core {a : V} (ar : a≠r) (ax : a∈tips) (aw : H.Adj a w) : T.Adj a w :=
    keep ⟨aw,by simpa [p,ax] using edges a ar⟩
  have rootEdge (a : V) (ra : H.Adj r a) (free : a∉tips) : T.Adj r a :=
    keep ⟨ra,(show K.Adj a r by simpa [p,free] using edges a ra.ne.symm).symm⟩
  refine ⟨T,sub,tr,?_,core ur (mem_insert_self ..) uw,core vr (mem_insert_of_mem (mem_singleton_self _)) vw⟩
  exact fun lf => st (leaf_unique T lf (rootEdge s rs (by simp [tips,su,sv])) (rootEdge t rt (by simp [tips,tu,tv])))

/-- Force the two spokes through w and two root edges into a spanning
parity tree when the specified root neighbors differ from the chord ends. -/
theorem parity_triangle_tree (J : SimpleGraph V) (jc : J.Connected) (r u v w s t : V)
    (ur : u≠r) (vr : v≠r) (uw : J.Adj u w) (vw : J.Adj v w)
    (rs : J.Adj r s) (rt : J.Adj r t) (st : s≠t)
    (su : s≠u) (sv : s≠v) (tu : t≠u) (tv : t≠v) (odd : Bool)
    (op : ∀ z∈({u,v}:Finset V), (z∈parity J r odd ↔ w∉parity J r odd)) :
    ∃ T≤J, T.IsTree ∧ (∀ {i j}, T.Adj i j → (i∈parity J r odd ↔ j∉parity J r odd)) ∧
      r∉leaves T ∧ T.Adj u w ∧ T.Adj v w := by
  let H := alternating J (parity J r odd)
  obtain ⟨con,star⟩ := alternating_parity J jc r odd
  obtain ⟨T,sub,tr,internal,xw,yw⟩ := prescribed_spokes H con r u v w s t ur vr
    ⟨uw,op u (mem_insert_self ..)⟩ ⟨vw,op v (mem_insert_of_mem (mem_singleton_self _))⟩
    (star s rs) (star t rt) st su sv tu tv
  exact ⟨T,fun _ _ e => (sub e).1,tr,fun e => (sub e).2,internal,xw,yw⟩

/-- An optimal tree containing the two triangle spokes gains a leaf
whenever their eligible common vertex has degree at most two. -/
theorem optimal_middle_gain (J T : SimpleGraph V) [DecidableRel T.Adj]
    (hn : 3<Fintype.card V) (u v w : V) (uv : u≠v) (tr : T.IsTree) (sub : T≤J)
    (U : Finset V) (opt : (U∩leaves T).card=weightedLeaves J U)
    (uw : T.Adj u w) (vw : T.Adj v w) (elig : w∈U) (bound : T.degree w≤2) :
    weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge u v) U := by
  classical
  have only (i : V) (e : T.Adj w i) : i=u ∨ i=v := by
    by_contra! no
    have inc : ({i,u,v}:Finset V)⊆T.neighborFinset w := by
      intro x mem
      simp only [mem_insert,mem_singleton] at mem
      rcases mem with rfl|rfl|rfl
      · exact (T.mem_neighborFinset ..).mpr e
      · exact (T.mem_neighborFinset ..).mpr uw.symm
      · exact (T.mem_neighborFinset ..).mpr vw.symm
    have cc := card_le_card inc
    rw [card_insert_of_not_mem (by simp [no]),card_pair uv,card_neighborFinset_eq_degree] at cc
    omega
  have free : u∉U∩leaves T ∨ v∉U∩leaves T := by
    by_contra! no
    obtain ⟨z,out⟩ : ∃ z, z∉({w,u,v}:Finset V) := by
      by_contra! noZ
      have c := card_le_card (show univ⊆({w,u,v}:Finset V) from fun x _ => noZ x)
      rw [card_univ,card_insert_of_not_mem (by simp [uw.ne.symm,vw.ne.symm]),card_pair uv] at c
      omega
    have nz := (show z≠w ∧ z≠u ∧ z≠v by simpa using out)
    obtain ⟨k,wk,dk⟩ := Graffiti169.exists_predecessor T tr.isConnected z w nz.1.symm
    have leaf : k∈leaves T := (only k wk).elim (fun h => h ▸ (mem_inter.mp no.1).2) (fun h => h ▸ (mem_inter.mp no.2).2)
    have kz : k≠z := by rcases only k wk with rfl|rfl <;> tauto
    obtain ⟨q,kq,dq⟩ := Graffiti169.exists_predecessor T tr.isConnected z k kz
    rw [leaf_unique T leaf kq wk.symm] at dq
    omega
  have rotate {x y : V} (xy : x≠y) (xw : T.Adj x w) (yw : T.Adj y w)
      (two : ∀ i, T.Adj w i → i=y ∨ i=x) (ok : x∉U∩leaves T) :
      weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge x y) U := by
    have side : (T.deleteEdges {s(w,y)}).Reachable w x :=
      (show (T.deleteEdges {s(w,y)}).Adj w x from deleteEdges_adj.mpr ⟨xw.symm,by simp [Sym2.eq_iff,xy,xw.ne,yw.ne]⟩).reachable
    exact rotation_gain _ (by omega) J T le_sup_left sub tr U opt x y w x
      (Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)) xw.ne yw.symm xw.symm xy.symm two elig ok side
  rcases free with h|h
  · exact rotate uv uw vw (fun i e => (only i e).symm) h
  · rw [edge_comm]; exact rotate uv.symm vw uw only h

/-- On a tight lower instance one vertex short of bipartite order, a
two-edge parity path through an eligible vertex supplies a winning
rotation whenever it can coexist with an internal root. -/
theorem rank_two_triangle_gain (J T : SimpleGraph V) [DecidableRel T.Adj]
    (hn : 3<Fintype.card V) (r u v w : V) (uv : u≠v)
    (tr : T.IsTree) (sub : T≤J) (root : r∉leaves T) (A P : Finset V)
    (ai : Indep J A) (ne : A≠P) (cross : ∀ {i j}, T.Adj i j → (i∈P ↔ j∉P))
    (rank : bipartiteNum J+1=Fintype.card V) (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (uw : T.Adj u w) (vw : T.Adj v w) (elig : w∈eligible A P r) :
    weightedLeaves J (eligible A P r)<weightedLeaves (J⊔SimpleGraph.edge u v) (eligible A P r) := by
  classical
  obtain ⟨opt,deg,_⟩ := one_defect_rigid J T tr sub (by omega) r root A P ai ne cross rank tight
  have bound := deg w (mem_union.mpr (eligible_iff.mp elig).1)
  exact optimal_middle_gain J T hn u v w uv tr sub _ opt uw vw elig bound

/-- All rank deficits are covered when a forced-spoke parity tree separates
the symmetric difference into at least as many components as the deficit. -/
theorem forest_gap_triangle_gain (J T : SimpleGraph V) [DecidableRel T.Adj]
    (hn : 3<Fintype.card V) (r u v w : V) (uv : u≠v) (tr : T.IsTree) (sub : T≤J)
    (root : r∉leaves T) (A P : Finset V) (ai : Indep J A)
    (cross : ∀ {i j}, T.Adj i j → (i∈P ↔ j∉P))
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (gap : let D := (A∪P)\(A∩P)
           (T.edgeFinset∩D.sym2).card+Fintype.card V≤D.card+bipartiteNum J)
    (uw : T.Adj u w) (vw : T.Adj v w) (elig : w∈eligible A P r) :
    weightedLeaves J (eligible A P r)<weightedLeaves (J⊔SimpleGraph.edge u v) (eligible A P r) := by
  obtain ⟨opt,deg⟩ := rigid_of_forest_gap J T tr sub (by omega) r root A P ai cross tight gap
  exact optimal_middle_gain J T hn u v w uv tr sub _ opt uw vw elig (deg w (mem_union.mpr (eligible_iff.mp elig).1))

/-- A connected alternating subgraph certifies gain at arbitrary bipartite
rank when it retains the four prescribed edges and sufficiently few
edges internal to the symmetric difference. -/
theorem subgraph_gap_triangle_gain (J H : SimpleGraph V) [DecidableRel H.Adj]
    (hn : 3<Fintype.card V) (conn : H.Connected) (hj : H≤J) (r u v w s t : V) (uv : u≠v)
    (ur : u≠r) (vr : v≠r) (uw : H.Adj u w) (vw : H.Adj v w)
    (rs : H.Adj r s) (rt : H.Adj r t) (st : s≠t) (su : s≠u) (sv : s≠v) (tu : t≠u) (tv : t≠v)
    (A P : Finset V) (ai : Indep J A) (cross : ∀ {i j}, H.Adj i j → (i∈P ↔ j∉P))
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (gap : let D := (A∪P)\(A∩P)
           (H.edgeFinset∩D.sym2).card+Fintype.card V≤D.card+bipartiteNum J)
    (elig : w∈eligible A P r) :
    weightedLeaves J (eligible A P r)<weightedLeaves (J⊔SimpleGraph.edge u v) (eligible A P r) := by
  classical
  let D := (A∪P)\(A∩P)
  obtain ⟨T,th,tr,root,xw,yw⟩ := prescribed_spokes H conn r u v w s t ur vr uw vw rs rt st su sv tu tv
  have inc : T.edgeFinset∩D.sym2⊆H.edgeFinset∩D.sym2 := by
    intro e mem
    refine mem_inter.mpr ⟨?_,(mem_inter.mp mem).2⟩
    exact edgeFinset_mono th (mem_inter.mp mem).1
  have count := card_le_card inc
  apply forest_gap_triangle_gain J T hn r u v w uv tr (th.trans hj) root A P ai (fun e => cross (th e)) tight _ xw yw elig
  change (H.edgeFinset∩D.sym2).card+Fintype.card V≤D.card+bipartiteNum J at gap
  change (T.edgeFinset∩D.sym2).card+Fintype.card V≤D.card+bipartiteNum J
  omega

/-- A forest on D with |D|-1 edges contains the tree route between any
two marked ends. The two-spoke form singles out their common middle. -/
theorem forest_middle (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (D : Finset V)
    (card : (T.edgeFinset∩D.sym2).card+1=D.card) (u v w : V) (uv : u≠v)
    (ud : u∈D) (vd : v∈D) (uw : T.Adj u w) (vw : T.Adj v w) : w∈D := by
  classical
  obtain ⟨p,spec,formula⟩ := parent_edge_count T tr u D
  have eq := eq_of_subset_of_card_le (filter_subset (fun x => p x∈D) (D.erase u)) (by
    have := card_erase_add_one ud; omega)
  have keep (x : V) (dx : x∈D) (ne : x≠u) : p x∈D := by
    have mem : x∈D.erase u := mem_erase.mpr ⟨ne,dx⟩
    rw [← eq] at mem
    exact (mem_filter.mp mem).2
  by_contra out
  let H := T.deleteEdges {s(v,w)}
  have down (x : V) (dx : x∈D) : H.Reachable x u := by
    induction num : T.dist x u using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases ne : x=u
      · subst x; exact .refl _
      have pd := keep x dx ne
      obtain ⟨step,d⟩ := spec x ne
      have e : H.Adj x (p x) := deleteEdges_adj.mpr ⟨step,fun bad => by
        rcases Sym2.eq_iff.mp (show s(x,p x)=s(v,w) from bad) with ⟨_,pw⟩|⟨xw,_⟩
        · exact out (pw ▸ pd)
        · exact out (xw ▸ dx)⟩
      exact e.reachable.trans (ih _ (by omega) (p x) pd rfl)
  have last : H.Adj u w := deleteEdges_adj.mpr ⟨uw,by simp [Sym2.eq_iff,uv,uw.ne]⟩
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp tr.IsAcyclic vw)).2 ((down v vd).trans last.reachable)

/-- A concrete sufficient condition in the triangle case with two
vertices omitted from the upper bipartite order. Depth at least two
ensures that both root-star edges can avoid the chord endpoints. -/
theorem crossing_middle_gain (J : SimpleGraph V) (jc : J.Connected) (hn : 3<Fintype.card V)
    (r u v w : V) (uv : u≠v) (flat : J.dist u r=J.dist v r) (deep : 2≤J.dist u r)
    (two : ∃ s t, J.Adj r s ∧ J.Adj r t ∧ s≠t) (uw : J.Adj u w) (vw : J.Adj v w)
    (odd : Bool) (A : Finset V) (ai : Indep J A) (ne : A≠parity J r odd)
    (across : w∈parity J r odd ↔ u∉parity J r odd)
    (rank : bipartiteNum J+1=Fintype.card V)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card)
    (marked : w∈eligible A (parity J r odd) r ∨
      (u∉A∩parity J r odd ∧ v∉A∩parity J r odd)) :
    weightedLeaves J (eligible A (parity J r odd) r)<weightedLeaves (J⊔SimpleGraph.edge u v) (eligible A (parity J r odd) r) := by
  classical
  obtain ⟨s,t,rs,rt,st⟩ := two
  have fr {z} (d : 2≤J.dist z r) : z≠r := by rintro rfl; rw [dist_self] at d; omega
  have avoid {a z} (e : J.Adj r a) (d : 2≤J.dist z r) : a≠z := by
    rintro rfl
    rw [dist_eq_one_iff_adj.mpr e.symm] at d
    omega
  have dv : 2≤J.dist v r := flat ▸ deep
  have eqp : v∈parity J r odd ↔ u∈parity J r odd := by simp only [mem_parity,flat]
  have op (z : V) (h : z∈({u,v}:Finset V)) : z∈parity J r odd ↔ w∉parity J r odd := by
    rcases (show z=u ∨ z=v by simpa using h) with rfl|rfl <;> tauto
  obtain ⟨T,sub,tr,cross,internal,xw,yw⟩ := parity_triangle_tree J jc r u v w s t
    (fr deep) (fr dv) uw vw rs rt st (avoid rs deep) (avoid rs dv) (avoid rt deep) (avoid rt dv) odd op
  let P := parity J r odd
  let D := (A∪P)\(A∩P)
  have wr : w≠r := by
    rintro rfl
    rw [dist_eq_one_iff_adj.mpr uw] at deep
    omega
  have mark (hw : w∈A∪P) : w∈eligible A P r :=
    eligible_iff.mpr ⟨mem_union.mp hw,Or.inl wr⟩
  have elig : w∈eligible A P r := by
    rcases marked with h|⟨cu,cv⟩
    · exact h
    by_cases wp : w∈P
    · exact mark (mem_union_right _ wp)
    have up : u∈P := Classical.byContradiction (fun no => wp (across.mpr no))
    have ud : u∈D := mem_sdiff.mpr ⟨mem_union_right _ up,cu⟩
    have vd : v∈D := mem_sdiff.mpr ⟨mem_union_right _ (eqp.mpr up),cv⟩
    obtain ⟨_,_,count⟩ := one_defect_rigid J T tr sub (by omega) r internal A P ai ne cross rank tight
    have wd := forest_middle T tr D count u v w uv ud vd xw yw
    exact mark (mem_sdiff.mp wd).1
  exact rank_two_triangle_gain J T hn r u v w uv tr sub internal A _ ai ne cross rank tight xw yw elig

/-- Extend any choice of shortest-path predecessors to a parity spanning
tree containing the full root star. -/
theorem predecessor_tree (J : SimpleGraph V) (jc : J.Connected) (r : V) (odd : Bool)
    (p : V→V) (pred : ∀ x≠r, J.Adj x (p x) ∧ J.dist x r=J.dist (p x) r+1) :
    ∃ T≤J, T.IsTree ∧ (∀ {x y}, T.Adj x y → (x∈parity J r odd ↔ y∉parity J r odd)) ∧
      (∀ x≠r, T.Adj x (p x)) ∧ ∀ x, J.Adj r x → T.Adj r x := by
  classical
  obtain ⟨K,kt,ke⟩ := virtual_tree r p (fun x => J.dist x r) (fun x ne => by change J.dist (p x) r<J.dist x r; rw [(pred x ne).2]; omega)
  let H := alternating J (parity J r odd)
  obtain ⟨T,th,tr,keep⟩ := keep_target H K (alternating_parity J jc r odd).1 kt
  have take (x : V) (ne : x≠r) : T.Adj x (p x) := by
    obtain ⟨edge,down⟩ := pred x ne
    apply keep
    refine ⟨⟨edge,?_⟩,ke x ne⟩
    simp only [mem_parity,down]
    cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
  refine ⟨T,fun _ _ e => (th e).1,tr,fun e => (th e).2,take,?_⟩
  intro x rx
  have dist := (pred x rx.ne.symm).2
  rw [dist_eq_one_iff_adj.mpr rx.symm] at dist
  have eq : p x=r := jc.dist_eq_zero_iff.mp (by omega)
  simpa only [eq] using (take x rx.ne.symm).symm

#print axioms predecessor_tree
#print axioms prescribed_spokes
#print axioms subgraph_gap_triangle_gain
#print axioms optimal_middle_gain
#print axioms forest_gap_triangle_gain
#print axioms forest_middle
#print axioms rank_two_triangle_gain
#print axioms crossing_middle_gain
#print axioms block_neighbors
#print axioms rank_one_rooted
#print axioms bipartite_lower_chord
#print axioms parity_triangle_tree
end Minimal180
