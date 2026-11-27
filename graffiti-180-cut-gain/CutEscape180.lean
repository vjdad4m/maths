import CutChain180

set_option warningAsError true
namespace Minimal180.CutGain.TightCut
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {J : SimpleGraph V} {S T : Finset V} {x y w : V} {r : ↥S} {odd : Bool} {A : Finset V}
variable (h : TightCut J S T x y w r odd A)
include h

/-- A failed lower-deficit-one cut forces a strictly deeper horizontal
rank-dropping edge whose ends have no common predecessor. -/
theorem deeper_chord (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U →
      ∃ q z, q∈P ∧ q∉A ∧ z∈A∩P ∧ J.Adj q z ∧
        G.dist x r.val<G.dist q r.val ∧ G.dist q r.val=G.dist z r.val ∧
        bipartiteNum (G.deleteEdges {s(q,z)})=bipartiteNum G+1 ∧
        ¬∃ p,G.Adj q p ∧ G.Adj z p ∧ G.dist q r.val=G.dist p r.val+1 := by
  classical
  intro G P U ng
  let D := (A∪P)\(A∩P)
  obtain ⟨root,_,_⟩ := h.defect_one_entry rank1 ng
  change r.val∉D at root
  obtain ⟨cnt,t,tip,td,minimal,unique,arc⟩ := h.defect_one_chain rank1 ng
  change P.card=A.card+1 at cnt
  obtain ⟨_,xp,yp,_,_⟩ := h.defect_one_support rank1 ng
  have tips := mem_insert.mp tip
  have tp : t∈P := tips.elim (fun e => e ▸ xp) (fun e => mem_singleton.mp e ▸ yp)
  let Q := P.erase t
  have sizeQ : Q.card=A.card := by change (P.erase t).card=A.card; have z := card_erase_add_one tp; omega
  have subset : Q⊆P := erase_subset _ _
  have mask : eligible Q P r.val⊆U := by
    intro i hv
    obtain ⟨mark,safe⟩ := eligible_iff.mp hv
    have ip : i∈P := mark.elim (fun m => subset m) id
    refine eligible_iff.mpr ⟨Or.inr ip,?_⟩
    rcases safe with dif|both
    · exact Or.inl dif
    · right
      refine ⟨?_,both.2⟩
      apply Classical.byContradiction
      intro na
      exact root (mem_sdiff.mpr ⟨mem_union_right _ both.2,fun both => na (mem_inter.mp both).1⟩)
  have not_ind : ¬Indep G Q := by
    intro ind
    have b := confined_parity G (h.connected.mono le_sup_left) (by have := h.order; omega) r.val odd.toNat Q ind subset
    change 1+Q.card+P.card≤weightedLeaves G (eligible Q P r.val)+markedBip G (Q∩P) at b
    have maxb : markedBip G (Q∩P)≤bipartiteNum G := by
      apply Finset.sup_le
      exact fun _ k => size_bip G (mem_filter.mp k).2.2
    have le := eligible_mono G mask
    have tight := h.tight
    change weightedLeaves J U+bipartiteNum J=1+A.card+P.card at tight
    have rk : bipartiteNum J=bipartiteNum G+1 := h.rank
    omega
  unfold Indep at not_ind
  push_neg at not_ind
  obtain ⟨a,aq,b,bq,ab,edge⟩ := not_ind
  obtain ⟨q,qq,z,zq,qna,qz⟩ : ∃ q∈Q, ∃ z∈Q, q∉A ∧ G.Adj q z := by
    by_cases aa : a∈A
    · exact ⟨b,bq,a,aq,fun ba => h.independent _ aa _ ba ab edge,edge.symm⟩
    · exact ⟨a,aq,b,bq,aa,edge⟩
  obtain ⟨qt,qp⟩ := mem_erase.mp qq
  obtain ⟨zt,zp⟩ := mem_erase.mp zq
  have qd : q∈D := mem_sdiff.mpr ⟨mem_union_right _ qp,fun h => qna (mem_inter.mp h).1⟩
  have con : G.Connected := h.connected.mono le_sup_left
  have flat : G.dist q r.val=G.dist z r.val := by
    have l := con.dist_triangle (u:=q) (v:=z) (w:=r.val)
    have m := con.dist_triangle (u:=z) (v:=q) (w:=r.val)
    rw [dist_eq_one_iff_adj.mpr qz] at l
    rw [dist_eq_one_iff_adj.mpr qz.symm] at m
    have a := (mem_parity ..).mp qp
    have b := (mem_parity ..).mp zp
    change G.dist q r.val%2=odd.toNat at a
    change G.dist z r.val%2=odd.toNat at b
    omega
  obtain ⟨ds,_,_⟩ := seam_layers h.connected h.split h.farTip h.rightSpoke h.absent r h.horizontal
  have same : J.dist q r.val=J.dist z r.val := (ds q).symm.trans (flat.trans (ds z))
  have za : z∈A := by
    apply Classical.byContradiction
    intro zn
    have zd : z∈D := mem_sdiff.mpr ⟨mem_union_right _ zp,fun h => zn (mem_inter.mp h).1⟩
    exact qz.ne (unique q qd z zd same)
  have deep : J.dist t r.val<J.dist q r.val := lt_of_le_of_ne (minimal q qd)
    (fun eq => qt (unique q qd t td eq.symm))
  have dtx : G.dist t r.val=G.dist x r.val := tips.elim
    (fun e => congrArg (fun v => G.dist v r.val) e)
    (fun e => (congrArg (fun v => G.dist v r.val) (mem_singleton.mp e)).trans h.horizontal.symm)
  have deepG : G.dist x r.val<G.dist q r.val := by rw [←dtx,ds,ds]; exact deep
  have qx : q≠x := fun e => (Nat.lt_irrefl _) (e ▸ deepG)
  have qy : q≠y := by
    intro eq
    have fl : G.dist x r.val=G.dist y r.val := h.horizontal
    rw [eq,fl] at deepG
    exact Nat.lt_irrefl _ deepG
  have lower {p : V} (e : G.Adj q p) : J.Adj q p := by
    rcases e with e|e
    · exact e
    rcases ((edge_adj ..).mp e).1 with k|k
    · exact (qx k.1).elim
    · exact (qy k.1).elim
  obtain ⟨u,ud,pu⟩ := arc q qd qt
  have up : u∉P := by
    intro uP
    have dq := (mem_parity ..).mp qp
    have du := (mem_parity ..).mp uP
    change G.dist u r.val%2=odd.toNat at du
    change G.dist q r.val%2=odd.toNat at dq
    rw [ds] at dq du
    have diff := pu.2.1
    omega
  have ua : u∈A := (mem_union.mp (mem_sdiff.mp ud).1).resolve_right up
  refine ⟨q,z,qp,qna,mem_inter.mpr ⟨za,zp⟩,lower qz,deepG,flat,?_,?_⟩
  · apply h.sparse q z qz
    · intro ar
      have d := ar.2.1
      change G.dist z r.val=G.dist q r.val+1 at d
      omega
    · intro ar
      have d := ar.2.1
      change G.dist q r.val=G.dist z r.val+1 at d
      omega
  · rintro ⟨p,qp',zp',dp⟩
    have dep : J.dist q r.val=J.dist p r.val+1 := by rw [←ds,←ds]; exact dp
    have eq := pu.2.2 p (lower qp').symm dep
    exact h.independent z za u ua (eq ▸ zp'.ne) (eq ▸ zp')

#print axioms deeper_chord
end Minimal180.CutGain.TightCut
