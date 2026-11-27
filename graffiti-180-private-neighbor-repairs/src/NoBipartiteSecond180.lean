import BipartiteSparse180
import CoreSplit180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On the three vertices of a horizontal triangle, the root is the middle.
If that middle is eligible it belongs to both marks. Independence and
equal tip parity then force both old path leaves to be eligible. -/
theorem triangle_no_second (J G : SimpleGraph V) (jc : J.Connected) (gc : G.Connected)
    (jg : J≤G) (hn : 2<Fintype.card V) (x y w r : V) (xy : x≠y)
    (xw : J.Adj x w) (wy : J.Adj w y) (all : ({x,y,w}:Finset V)=univ)
    (hor : G.dist x r=G.dist y r) (odd : Bool) (A C : Finset V) (ind : Indep G A)
    (cu : C⊆eligible A (parity G r odd) r) (ct : C.card=weightedLeaves J (eligible A (parity G r odd) r)+1) :
    ¬NeedsTip J C (univ\C) x y := by
  classical
  intro tip
  let P := parity G r odd
  let U := eligible A P r
  have xr : x≠r := by
    intro eq
    have zero : G.dist y r=0 := hor.symm.trans (eq ▸ dist_self)
    exact xy (eq.trans (gc.dist_eq_zero_iff.mp zero).symm)
  have yr : y≠r := by
    intro eq
    have zero : G.dist x r=0 := hor.trans (eq ▸ dist_self)
    exact xy ((gc.dist_eq_zero_iff.mp zero).trans eq.symm)
  have rmem : r∈({x,y,w}:Finset V) := all ▸ mem_univ r
  have rw' : r=w := by
    simp only [mem_insert,mem_singleton] at rmem
    exact (rmem.resolve_left xr.symm).resolve_left yr.symm
  have wc : w∈C := by
    by_contra no
    exact tip.2.2.2.1 ⟨w,mem_sdiff.mpr ⟨mem_univ _,no⟩,xw⟩
  have rootmem : r∈U := rw' ▸ cu wc
  have wrA : w∈A := rw' ▸ ((eligible_iff.mp rootmem).2.resolve_left (fun h => h rfl)).1
  have xu := cu tip.1
  have xp : x∈P := (eligible_iff.mp xu).1.resolve_left (fun ax => ind x ax w wrA xw.ne (jg xw))
  have yp : y∈P := (mem_parity ..).mpr (hor ▸ ((mem_parity ..).mp xp))
  have yu : y∈U := eligible_iff.mpr ⟨Or.inr yp,Or.inl yr⟩
  have complement : (univ\({x,y}:Finset V))={w} := by
    rw [←all]
    ext i
    simp only [mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨h,no⟩
      rcases h with k|k|k
      · exact (no (Or.inl k)).elim
      · exact (no (Or.inr k)).elim
      · exact k
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl),fun h => h.elim xw.ne.symm wy.ne⟩
  have bound : 2≤weightedLeaves J U := by
    apply (score_iff_core J jc hn U 2).mpr
    refine ⟨{x,y},insert_subset xu (singleton_subset_iff.mpr yu),by rw [card_pair xy],
      complement ▸ con_single J w,?_⟩
    intro i hi
    rw [complement]
    rcases mem_insert.mp hi with rfl|other
    · exact ⟨w,mem_singleton_self _,xw⟩
    · exact ⟨w,mem_singleton_self _,mem_singleton.mp other ▸ wy.symm⟩
  have sub : C⊆{x,w} := by
    intro i hi
    have h : i∈({x,y,w}:Finset V) := all ▸ mem_univ i
    simp only [mem_insert,mem_singleton] at h ⊢
    exact h.elim Or.inl (fun k => Or.inr (k.resolve_left (fun iy => (mem_sdiff.mp tip.2.1).2 (iy ▸ hi))))
  have cap := card_le_card sub
  rw [card_pair xw.ne] at cap
  change C.card=weightedLeaves J U+1 at ct
  omega

/-- The first form holds at every tight horizontal, rooted-sparse, rank-drop
triangle transition whose lower graph has full bipartite order. -/
theorem bipartite_sparse_first (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (x y w r : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (odd : Bool) (A : Finset V) :
    let G := J⊔SimpleGraph.edge x y
    let P := parity G r odd
    let U := eligible A P r
    NoCut G → SparseAt G r → G.dist x r=G.dist y r → Indep G A →
    bipartiteNum J=Fintype.card V → bipartiteNum J=bipartiteNum G+1 →
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card → FirstForm J U x y w := by
  classical
  intro G P U block sp hor ind full drop tight
  have gc : G.Connected := jc.mono le_sup_left
  have order := (bipartite_lower_triangle_order J jc hn x y w r xy old xw wy block sp full drop).1
  have gain := bipartite_lower_chord G J gc hn block r odd A ind full drop tight
  obtain ⟨C,cu,wc,ct,which⟩ := (triangle_gain_iff_core J jc hn x y w xy old xw wy U).mp gain
  rcases which with win|direct|rev
  · exact ⟨C,cu,wc,ct,win⟩
  · exact (triangle_no_second J G jc gc le_sup_left hn x y w r xy xw wy order hor odd A C ind cu ct direct).elim
  · have order' : ({y,x,w}:Finset V)=univ := by rw [insert_comm y x,order]
    exact (triangle_no_second J G jc gc le_sup_left hn y x w r xy.symm wy.symm xw.symm order' hor.symm
      odd A C ind cu ct rev).elim

#print axioms triangle_no_second
#print axioms bipartite_sparse_first
end Minimal180.PrivateCore
