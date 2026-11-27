import ArmOutside180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The second edge of a single disagreement arm is a bridge in the
alternating graph. Removing this edge leaves the full root star available. -/
theorem second_bridge {G : SimpleGraph V} {r t s : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (rootTip : G.Adj r t) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    Spine G r (D.erase r) t → s∈D.erase r → Arc G r t s → ¬(carve G P t s).Reachable t s := by
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
  have rd : r∈D := h.root_disagreement
  have keepD {a : V} (ad : a∈D) (ra : M.Adj r a) : a=t :=
    sp.single a (mem_erase.mpr ⟨ra.ne.symm,ad⟩) t sp.tip
      ((dist_eq_one_iff_adj.mpr (mg ra).symm).trans (dist_eq_one_iff_adj.mpr rootTip.symm).symm)
  have cover : M.edgeFinset∩D.sym2 ⊆ insert s(r,t) (M.edgeFinset∩(D.erase r).sym2) := by
    intro e mem
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨edge,inside⟩ := mem_inter.mp mem
      obtain ⟨ad,bd⟩ := mk_mem_sym2_iff.mp inside
      have ab := mem_edgeFinset.mp edge
      by_cases ar : a=r
      · subst a
        exact mem_insert.mpr (Or.inl (by rw [keepD bd ab]))
      by_cases br : b=r
      · subst b
        exact mem_insert.mpr (Or.inl (by rw [keepD ad ab.symm,Sym2.eq_swap]))
      exact mem_insert_of_mem (mem_inter.mpr ⟨edge,mk_mem_sym2_iff.mpr ⟨mem_erase.mpr ⟨ar,ad⟩,mem_erase.mpr ⟨br,bd⟩⟩⟩)
  have bound := (card_le_card cover).trans (card_insert_le _ _)
  have size := card_erase_add_one rd
  change (M.edgeFinset∩D.sym2).card+1=D.card at edges
  have low := forest_strict M tree (D.erase r) ⟨t,sp.tip⟩
  obtain ⟨z,zd,tz⟩ := forest_has_neighbor M tree sp.tip sp.other (by omega)
  have bigger : G.dist t r<G.dist z r := lt_of_le_of_ne (sp.minimum z zd) (fun e => tz.ne (sp.single t sp.tip z zd e))
  have bound := h.connected.dist_triangle (u:=z) (v:=t) (w:=r)
  rw [dist_eq_one_iff_adj.mpr (mg tz).symm] at bound
  have dz := ts.2.1
  have zs := sp.single z zd s sd (by omega)
  have deleted := (deleteEdges_adj.mp (show K.Adj t z from mk tz)).2
  exact deleted (Set.mem_singleton_iff.mpr (zs ▸ rfl))


#print axioms second_bridge
end Minimal180.RootEar
