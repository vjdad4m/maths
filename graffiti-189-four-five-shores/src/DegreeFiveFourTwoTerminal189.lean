import DegreeFiveBothFiveResidual189
import ResidualOreParam189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports residue residue_count residual_neighbor_bound from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem terminal_four_port_two_common_at_most_six
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (C : Cmp (G:=G) (a:=a) (b:=b))
    (four : (cutPorts C).card=4) (two : (sharedPortSet C).card=2)
    (small : (Shore C).card≤6)
    (univ : ∀ x∈sharedPortSet C,∀ w∈Shore C,x≠w → G.Adj x w) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let K := sharedPortSet C
  let R := residue C
  let S := Shore C
  let E := cutPorts C \ K
  have k2 : K.card=2 := two
  have e2 : E.card=2 := by
    have h : E.card+K.card=(cutPorts C).card := card_sdiff_add_card_eq_card (common_sub_ports C)
    omega
  have eSub : E⊆R := by
    intro z ze
    obtain ⟨zp,zn⟩ := mem_sdiff.mp ze
    exact mem_sdiff.mpr ⟨(cut_mem_iff.mp zp).1,zn⟩
  have sum : R.card+K.card=S.card := residue_count C
  have smallR : R.card≤2*2 := by
    have h : S.card≤6 := small
    omega
  have pos : R.Nonempty := by
    obtain ⟨z,ze⟩ := card_pos.mp (show 0<E.card by omega)
    exact ⟨z,eSub ze⟩
  obtain ⟨x,y,xy,keq⟩ := card_eq_two.mp k2
  have xk : x∈K := by simp [keq]
  have yk : y∈K := by simp [keq]
  have xn : x∉R := fun h=>(mem_sdiff.mp h).2 xk
  have yn : y∉R := fun h=>(mem_sdiff.mp h).2 yk
  obtain ⟨xs,ax,bx⟩ := mem_filter.mp xk
  obtain ⟨ys,ay,by'⟩ := mem_filter.mp yk
  have eq : insert x (insert y R)=S := by
    have h : K∪R=S := union_sdiff_of_subset (show K⊆S from filter_subset _ _)
    rw [←h,keq]
    ext w
    simp
  have pair (v : V) (vr : v∈R) (w : V) (wr : w∈R) (vw : v≠w) :
      2≤(R.filter (G.Adj v)).card ∨ 2≤(R.filter (G.Adj w)).card := by
    have vb : G.degree v≤K.card+(R.filter (G.Adj v)).card+1 := residual_neighbor_bound vr
    have wb : G.degree w≤K.card+(R.filter (G.Adj w)).card+1 := residual_neighbor_bound wr
    exact (degree v w vw).imp (fun h=>by omega) (fun h=>by omega)
  by_cases hit : ∀ u∈R,(R.filter (G.Adj u)).card<2 → ∃ v∈R,G.Adj u v
  · obtain ⟨v,vr,w,wr,p⟩ := residual_route_if_low_not_isolated_at_d 2 R smallR pos pair hit
    have yv := univ y yk v (mem_sdiff.mp vr).1 (fun e=>yn (e.symm ▸ vr))
    have xw := univ x xk w (mem_sdiff.mp wr).1 (fun e=>xn (e.symm ▸ wr))
    have q := (p.prefix yv yn).suffix xw.symm (by simp [xy,xn])
    exact ⟨y,x,ay,bx,show RouteOn G S y x from eq ▸ q⟩
  push_neg at hit
  obtain ⟨z,zr,zd,iso⟩ := hit
  let Q := R.erase z
  have high (v : V) (vq : v∈Q) : 2≤(Q.filter (G.Adj v)).card := by
    obtain ⟨vz,vr⟩ := mem_erase.mp vq
    have he : Q.filter (G.Adj v)=R.filter (G.Adj v) := by
      ext w
      by_cases e : w=z
      · subst w; simp [Q,show ¬G.Adj v z from fun h=>iso v vr h.symm]
      simp [Q,e]
    rw [he]
    exact (pair z zr v vr vz.symm).resolve_left (by omega)
  obtain ⟨r,re,rz⟩ : ∃ r∈E,r≠z := by
    apply Classical.byContradiction
    intro h
    have p : E⊆{z} := fun v ve=>mem_singleton.mpr (Classical.byContradiction (fun e=>h ⟨v,ve,e⟩))
    have c := card_le_card p
    simp at c
    omega
  have rq : r∈Q := mem_erase.mpr ⟨rz,eSub re⟩
  obtain ⟨w,wq,p⟩ := rooted_high_residual_Ore_at_d 2 Q
    (le_trans (card_le_card (erase_subset _ _)) smallR) high rq
  have wr : w∈R := (mem_erase.mp wq).2
  have xx := univ x xk w (mem_sdiff.mp wr).1 (fun e=>xn (e.symm ▸ wr))
  have xz := univ x xk z (mem_sdiff.mp zr).1 (fun e=>xn (e.symm ▸ zr))
  have yz := univ y yk z (mem_sdiff.mp zr).1 (fun e=>yn (e.symm ▸ zr))
  have xq : x∉Q := fun h=>xn (mem_of_mem_erase h)
  have zx : z≠x := fun h=>xn (h ▸ zr)
  have yz' : y≠z := fun h=>yn (h.symm ▸ zr)
  have q := ((p.suffix xx.symm xq).suffix xz (by simp [Q,zx])).suffix yz.symm
    (by simp [Q,yz',xy.symm,yn])
  have all : insert y (insert z (insert x Q))=S := by
    rw [←eq]
    ext v
    by_cases vh : v=z
    · subst v; simp [zr]
    simp [Q,vh,or_left_comm,or_assoc]
  have full : RouteOn G S r y := all ▸ q
  rcases (cut_mem_iff.mp (mem_sdiff.mp re).1).2 with ar|br
  · exact ⟨r,y,ar,by',full⟩
  exact ⟨y,r,ay,br,full.reverse⟩

#print axioms terminal_four_port_two_common_at_most_six
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
