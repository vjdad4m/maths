import Spine180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def carve (J : SimpleGraph V) (P : Finset V) (t s : V) : SimpleGraph V :=
  (alternating J P).deleteEdges {s(t,s)}

omit [DecidableEq V] [Fintype V] in
theorem disconnected_ends {H : SimpleGraph V} (hc : H.Connected) {t s : V}
    (no : ¬(H.deleteEdges {s(t,s)}).Connected) : ¬(H.deleteEdges {s(t,s)}).Reachable t s := by
  intro alt
  let K := H.deleteEdges {s(t,s)}
  have route {a b : V} (p : H.Walk a b) : K.Reachable a b := by
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b _ e _ ih =>
      apply Reachable.trans _ ih
      by_cases pair : s(a,b)=s(t,s)
      · rcases Sym2.eq_iff.mp pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact alt
        · exact alt.symm
      · exact (show K.Adj a b from deleteEdges_adj.mpr ⟨e,pair⟩).reachable
  exact no ((connected_iff_exists_forall_reachable _).mpr ⟨t,fun a => route (hc t a).some⟩)

theorem forest_has_neighbor (M : SimpleGraph V) [DecidableRel M.Adj] (tree : M.IsTree)
    {D : Finset V} {t : V} (td : t∈D) (more : (D.erase t).Nonempty)
    (count : (M.edgeFinset∩D.sym2).card+1=D.card) : ∃ s∈D,M.Adj t s := by
  classical
  by_contra! no
  have sub : M.edgeFinset∩D.sym2⊆M.edgeFinset∩(D.erase t).sym2 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨edge,inside⟩ := mem_inter.mp he
      obtain ⟨ad,bd⟩ := mk_mem_sym2_iff.mp inside
      have ab := mem_edgeFinset.mp edge
      exact mem_inter.mpr ⟨edge,mk_mem_sym2_iff.mpr ⟨mem_erase.mpr ⟨fun eq => no b bd (eq ▸ ab),ad⟩,
        mem_erase.mpr ⟨fun eq => no a ad (eq ▸ ab.symm),bd⟩⟩⟩
  have strict := (card_le_card sub).trans_lt (forest_strict M tree (D.erase t) more)
  have c := card_erase_add_one td
  omega

theorem spine_bridge {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (one : bipartiteNum J+1=Fintype.card V) (t s : V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let D := (A∪P)\(A∩P)
    Spine J r.val D t → s∈D → Arc J r.val t s → ¬(carve J P t s).Reachable t s := by
  classical
  intro G P D sp sd ts
  let H := alternating J P
  let K := carve J P t s
  have switchP : parity J r.val odd=P := h.layers_eq
  obtain ⟨hc,star⟩ := alternating_parity J h.connected r.val odd
  rw [switchP] at hc star
  apply disconnected_ends hc
  intro kc
  change K.Connected at kc
  have rs : r.val≠s := fun eq => sp.root (eq ▸ sd)
  have rt : r.val≠t := fun eq => sp.root (eq ▸ sp.tip)
  have keep {i : V} (ri : J.Adj r.val i) : K.Adj r.val i := by
    apply deleteEdges_adj.mpr
    refine ⟨star i ri,?_⟩
    intro pair
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair) with a|a
    · exact rt a.1
    · exact rs a.1
  obtain ⟨_,dx,dy⟩ := seam_layers h.connected h.split h.farTip h.rightSpoke h.absent r h.horizontal
  have root_not {i : V} (d : J.dist i r.val=J.dist w r.val+1) : r.val≠i := by
    intro eq; rw [←eq,dist_self] at d; omega
  have before {i : V} (e : G.Adj r.val i) : J.Adj r.val i := by
    rcases e with e|e
    · exact e
    rcases ((edge_adj ..).mp e).1 with a|a
    · exact (root_not dx a.1).elim
    · exact (root_not dy a.1).elim
  obtain ⟨i,j,ei,ej,ij⟩ := block_neighbors G (h.connected.mono le_sup_left) (by have := h.order; omega) h.block r.val
  obtain ⟨F,fk,ft⟩ := kc.exists_isTree_le
  obtain ⟨M,mk,tree,full,_⟩ := full_star_exchange K F fk ft (by have := h.order; omega) r.val
  have internal : r.val∉leaves M := fun l => ij (leaf_unique M l (full i (keep (before ei))) (full j (keep (before ej))))
  have mh : M≤H := mk.trans (H.deleteEdges_le _)
  have mj : M≤J := fun _ _ e => (mh e).1
  have ne : A≠P := by
    intro eq
    have mem := sp.tip
    change t∈(A∪P)\(A∩P) at mem
    simp [eq] at mem
  have ai : Indep J A := fun a am b bm n e => h.independent a am b bm n (Or.inl e)
  obtain ⟨_,_,edges⟩ := one_defect_rigid J M tree mj (by have := h.order; omega) r.val internal A P ai ne (fun e => (mh e).2) one h.tight
  obtain ⟨z,zd,tz⟩ := forest_has_neighbor M tree sp.tip sp.other edges
  have distinct : z≠t := tz.ne.symm
  have bigger : J.dist t r.val<J.dist z r.val :=
    lt_of_le_of_ne (sp.minimum z zd) (fun e => distinct (sp.single z zd t sp.tip e.symm))
  have bound := h.connected.dist_triangle (u:=z) (v:=t) (w:=r.val)
  rw [dist_eq_one_iff_adj.mpr (mj tz).symm] at bound
  have dz := ts.2.1
  have zs := sp.single z zd s sd (by omega)
  have deleted := (deleteEdges_adj.mp (show K.Adj t z from mk tz)).2
  exact deleted (Set.mem_singleton_iff.mpr (zs ▸ rfl))

#print axioms spine_bridge
end Minimal180.DescentOne
