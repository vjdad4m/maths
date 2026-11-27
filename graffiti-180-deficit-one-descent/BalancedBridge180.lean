import BalancedSpine180
import Unmarked180
import SpineColor180

set_option warningAsError true
namespace Minimal180.DescentOne.FailedTwo
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V} (h : FailedTwo G r odd A)
include h

theorem free_independent {t w : V} :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    let U := eligible A P r
    Spine G r D t → G.Adj t w → w∉A∪P → U=A∪P → Indep G (univ\(A∪P)) := by
  classical
  intro P D U sp tw nw cover
  let I := A∩P
  have impossible (a b : V) (aa : a∉A∪P) (bb : b∉A∪P) (aw : a≠w) (ab : G.Adj a b) : False := by
    have noD {i : V} (out : i∉A∪P) : i∉D := fun m => out (mem_sdiff.mp m).1
    have noI {i : V} (out : i∉A∪P) : i∉I := fun m => out (mem_union_left _ (mem_inter.mp m).1)
    obtain ⟨M,mg,tree,edge,leaf,p,d,step⟩ := spine_tree (G:=G) (J:=G) le_rfl h.block (by have := h.order; omega)
      sp (noD nw) tw (noD aa) (noD bb) aw ab
    have iu : I⊆U := cover ▸ (inter_subset_left.trans subset_union_left)
    have du : D⊆U := cover ▸ sdiff_subset
    have dis : Disjoint I D := disjoint_left.mpr fun _ a b => (mem_sdiff.mp b).2 a
    have ind : Indep M I := fun i im j jm ne e => h.independent i (mem_inter.mp im).1 j (mem_inter.mp jm).1 ne (mg e)
    have lower := count_spine M tree (by have := h.order; omega) I D U ind iu du dis
      (noI aa) (noI bb) (noD aa) (noD bb) (noI nw) edge leaf p d step
    have upper : (U∩leaves M).card≤weightedLeaves G U := le_sup (f:=fun K => (U∩leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,mg,tree⟩)
    have bad := h.bad
    change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at bad
    have rk := h.rank
    have ci := card_union_add_card_inter A P
    have ii : I⊆A∪P := inter_subset_left.trans subset_union_left
    have cd := card_sdiff_add_card_eq_card ii
    change D.card+I.card=(A∪P).card at cd
    change (A∪P).card+I.card=A.card+P.card at ci
    omega
  intro i im j jm ne e
  by_cases iw : i=w
  · exact impossible j i (mem_sdiff.mp jm).2 (mem_sdiff.mp im).2 (by intro eq; exact ne (iw.trans eq.symm)) e.symm
  · exact impossible i j (mem_sdiff.mp im).2 (mem_sdiff.mp jm).2 iw e

theorem bridge {t s : V} :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    Spine G r D t → s∈D → Arc G r t s → ¬(carve G P t s).Reachable t s := by
  classical
  intro P D sp sd ts
  let H := alternating G P
  let K := carve G P t s
  obtain ⟨hc,star⟩ := alternating_parity G h.connected r odd
  apply disconnected_ends hc
  intro kc
  change K.Connected at kc
  have rs : r≠s := fun eq => sp.root (eq ▸ sd)
  have rt : r≠t := fun eq => sp.root (eq ▸ sp.tip)
  have keep {i : V} (ri : G.Adj r i) : K.Adj r i := by
    apply deleteEdges_adj.mpr
    refine ⟨star i ri,?_⟩
    intro pair
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair) with a|a
    · exact rt a.1
    · exact rs a.1
  obtain ⟨i,j,ei,ej,ij⟩ := block_neighbors G h.connected h.order h.block r
  obtain ⟨F,fk,ft⟩ := kc.exists_isTree_le
  obtain ⟨M,mk,tree,full,_⟩ := full_star_exchange K F fk ft (by have := h.order; omega) r
  have internal : r∉leaves M := fun l => ij (leaf_unique M l (full i (keep ei)) (full j (keep ej)))
  have mh : M≤H := mk.trans (H.deleteEdges_le _)
  have mg : M≤G := fun _ _ e => (mh e).1
  have edges := (h.rigid M tree mg internal fun e => (mh e).2).2
  obtain ⟨z,zd,tz⟩ := forest_has_neighbor M tree sp.tip sp.other edges
  have bigger : G.dist t r<G.dist z r := lt_of_le_of_ne (sp.minimum z zd) (fun e => tz.ne (sp.single t sp.tip z zd e))
  have bound := h.connected.dist_triangle (u:=z) (v:=t) (w:=r)
  rw [dist_eq_one_iff_adj.mpr (mg tz).symm] at bound
  have dz := ts.2.1
  have zs := sp.single z zd s sd (by omega)
  have deleted := (deleteEdges_adj.mp (show K.Adj t z from mk tz)).2
  exact deleted (Set.mem_singleton_iff.mpr (zs ▸ rfl))

#print axioms free_independent
#print axioms bridge
end Minimal180.DescentOne.FailedTwo
