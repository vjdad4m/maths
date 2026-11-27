import Bypass180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem path_interior_disjoint (T : SimpleGraph V) {u v : V} (p : T.Walk u v) (hp : p.IsPath) :
    Disjoint (leaves T) (interior p) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x lf inside
  obtain ⟨xv,xu,supp⟩ : x≠v ∧ x≠u ∧ x∈p.support := by simpa [interior] using inside
  obtain ⟨i,hi,lim⟩ := Walk.mem_support_iff_exists_getVert.mp supp
  have pos : i≠0 := by rintro rfl; exact xu (by simpa using hi.symm)
  have lt : i<p.length := by
    by_contra! no
    exact xv (hi.symm.trans (p.getVert_of_length_le no))
  have prev := (p.adj_getVert_succ (i:=i-1) (by omega)).symm
  rw [show i-1+1=i by omega,hi] at prev
  have after := p.adj_getVert_succ lt
  rw [hi] at after
  have same := leaf_unique T lf prev after
  have impossible := hp.getVert_injOn (by change i-1≤p.length; omega) (by change i+1≤p.length; omega) same
  omega

/-- Exact deletion formula. The old eligible-leaf optimum is the largest
new optimum after suppressing the strict interior of one old endpoint path. -/
theorem path_maximum (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (uv : u≠v) (U : Finset V) :
    (∀ (p : J.Walk u v), p.IsPath →
       weightedLeaves (J⊔SimpleGraph.edge u v) (U\interior p)≤weightedLeaves J U) ∧
    ∃ p : J.Walk u v, p.IsPath ∧
       weightedLeaves (J⊔SimpleGraph.edge u v) (U\interior p)=weightedLeaves J U := by
  classical
  let G := J⊔SimpleGraph.edge u v
  have bound (p : J.Walk u v) (hp : p.IsPath) : weightedLeaves G (U\interior p)≤weightedLeaves J U := by
    have dis : Disjoint (U\interior p) (interior p) := Finset.disjoint_left.mpr
      (fun x h y => (mem_sdiff.mp h).2 y)
    rw [show weightedLeaves G (U\interior p)=_ from bypass_no_gain J jc hn u v uv _ p hp dis]
    obtain ⟨S,sj,st,opt⟩ := tree_opt J jc (U\interior p)
    rw [← opt]
    have incl : (U\interior p)∩leaves S⊆U∩leaves S := fun _ hx => mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp hx).1).1,(mem_inter.mp hx).2⟩
    exact (card_le_card incl).trans (le_sup (f:=fun K => (U∩leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,sj,st⟩))
  refine ⟨bound,?_⟩
  obtain ⟨T,tj,tr,opt⟩ := tree_opt J jc U
  obtain ⟨route⟩ := tr.isConnected u v
  let p := route.toPath.val
  have simple : p.IsPath := route.toPath.property
  let q := p.mapLe tj
  have qpath : q.IsPath := simple.mapLe tj
  have same : interior q=interior p := by simp [interior,q,Walk.mapLe,Walk.support_map]
  have dis := path_interior_disjoint T p simple
  have sameSet : (U\interior q)∩leaves T=U∩leaves T := by
    rw [same]
    ext w
    simp only [mem_inter,mem_sdiff]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,fun k => Finset.disjoint_left.mp dis h.2 k⟩,h.2⟩
  refine ⟨q,qpath,le_antisymm (bound q qpath) ?_⟩
  rw [← opt,← sameSet]
  exact le_sup (f:=fun K => ((U\interior q)∩leaves K).card)
    (mem_filter.mpr ⟨mem_univ _,tj.trans (show J≤G from le_sup_left),tr⟩)

/-- Strict gain is equivalent to a loss for every path when its interior
is removed from the upper eligibility set. -/
theorem gain_iff_all_paths (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (uv : u≠v) (U : Finset V) :
    weightedLeaves J U < weightedLeaves (J⊔SimpleGraph.edge u v) U ↔
    ∀ (p : J.Walk u v), p.IsPath → weightedLeaves (J⊔SimpleGraph.edge u v) (U\interior p) <
      weightedLeaves (J⊔SimpleGraph.edge u v) U := by
  obtain ⟨bound,p,hp,eq⟩ := path_maximum J jc hn u v uv U
  exact ⟨fun lt q hq => (bound q hq).trans_lt lt,fun all => eq ▸ all p hp⟩

/-- The eligible leaves of every maximizing upper tree must separate the
endpoints internally on every old path, and this condition suffices. -/
theorem gain_iff_leaf_separator (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (u v : V) (uv : u≠v) (U : Finset V) :
    weightedLeaves J U < weightedLeaves (J⊔SimpleGraph.edge u v) U ↔
    ∀ T≤J⊔SimpleGraph.edge u v, T.IsTree → (U∩leaves T).card=weightedLeaves (J⊔SimpleGraph.edge u v) U →
    ∀ (p : J.Walk u v), p.IsPath → ((U∩leaves T)∩interior p).Nonempty := by
  classical
  constructor
  · intro gain T sub tr opt p hp
    have bound := path_gain_bound J hn u v uv U p hp T sub tr
    rw [opt] at bound
    exact card_pos.mp (by omega)
  · intro sep
    apply Classical.byContradiction
    intro no
    have eq := le_antisymm (Nat.le_of_not_gt no) (leaf_mono _ le_sup_left U)
    obtain ⟨T,tj,tr,opt⟩ := tree_opt J jc U
    obtain ⟨w⟩ := tr.isConnected u v
    let p := w.toPath.val
    have simple : p.IsPath := w.toPath.property
    let q := p.mapLe tj
    have same : interior q=interior p := by simp [interior,q,Walk.mapLe,Walk.support_map]
    obtain ⟨x,hx⟩ := sep T (tj.trans le_sup_left) tr (opt.trans eq.symm) q (simple.mapLe tj)
    rw [same] at hx
    exact Finset.disjoint_left.mp (path_interior_disjoint T p simple) (mem_inter.mp (mem_inter.mp hx).1).2 (mem_inter.mp hx).2

/-- Rooted biconnected criterion in terms of the leaves of upper optimizers. -/
def SeparatingBlocks : Prop := ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → 1<Fintype.card V → NoCut G → ∀ r, SparseAt G r → ∀ odd A, Indep G A →
    ∀ a b, G.Adj a b → G.dist a r=G.dist b r →
    let J := G.deleteEdges {s(a,b)}
    let P := parity G r odd
    let U := eligible A P r
    bipartiteNum J=bipartiteNum G+1 → weightedLeaves J U+bipartiteNum J=1+A.card+P.card →
    ∀ T≤G, T.IsTree → (U∩leaves T).card=weightedLeaves G U →
    ∀ (p : J.Walk a b), p.IsPath → ((U∩leaves T)∩interior p).Nonempty

theorem universal_iff_separating_blocks : Universal.{u} ↔ SeparatingBlocks.{u} := by
  rw [universal_iff_horizontal]
  have convert {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W) (hc : G.Connected)
      (hn : 1<Fintype.card W) (r a b : W) (e : G.Adj a b) (level : G.dist a r=G.dist b r)
      (U : Finset W) :
      let J := G.deleteEdges {s(a,b)}
      weightedLeaves J U<weightedLeaves G U ↔
      ∀ T≤G, T.IsTree → (U∩leaves T).card=weightedLeaves G U →
      ∀ (p : J.Walk a b), p.IsPath → ((U∩leaves T)∩interior p).Nonempty := by
    let J := G.deleteEdges {s(a,b)}
    have ab : ¬Arc G r a b := fun z => by have := z.2.1; omega
    have ba : ¬Arc G r b a := fun z => by have := z.2.1; omega
    have jc := (remove_edge_distances G hc r a b ab ba).1
    have restore : J⊔SimpleGraph.edge a b=G := by
      apply le_antisymm (sup_le (G.deleteEdges_le _) (by rw [← sup_eq_left]; exact sup_edge_of_adj G e))
      intro x y xy
      by_cases h : s(x,y)=s(a,b)
      · exact Or.inr ((adj_edge ..).mpr ⟨h.symm,xy.ne⟩)
      · exact Or.inl (deleteEdges_adj.mpr ⟨xy,h⟩)
    have result := gain_iff_leaf_separator J jc hn a b e.ne U
    rw [restore] at result
    exact result
  constructor
  · intro h V _ _ G hc hn noc r sp odd A ind a b edge level
    dsimp only
    intro rank tight
    exact (convert G hc hn r a b edge level _).mp (h V G hc hn noc r sp odd A ind a b edge level rank tight)
  · intro h V _ _ G hc hn noc r sp odd A ind a b edge level
    dsimp only
    intro rank tight
    exact (convert G hc hn r a b edge level _).mpr (h V G hc hn noc r sp odd A ind a b edge level rank tight)

#print axioms universal_iff_separating_blocks
#print axioms gain_iff_leaf_separator
#print axioms path_maximum
#print axioms gain_iff_all_paths
end Minimal180
