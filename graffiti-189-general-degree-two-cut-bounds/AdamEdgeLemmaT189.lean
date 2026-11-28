import AdamEdgeTEconomy189

namespace Graffiti189.AdamEdge
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem conditional_lemma_T (hc : G.Connected) {a b x z p q : V}
    (ax : G.Adj a x) (bz : G.Adj b z) (ap : G.Adj a p) (bq : G.Adj b q)
    (dab : G.dist a b=3)
    (X Y : Finset V) (xX : x∈X) (zX : z∈X) (pY : p∈Y) (qY : q∈Y)
    (aX : a∉X) (bX : b∉X) (aY : a∉Y) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v)
    (x2 : G.dist b x=2) (z2 : G.dist a z=2) (p3 : G.dist b p=3) (q3 : G.dist a q=3)
    (noOddP : XOdd G X a b p=∅) (noOddQ : XOdd G X b a q=∅)
    (noBadP : Bad G Y a b p=∅) (noBadQ : Bad G Y b a q=∅)
    (d : ℕ) (dl : 6≤d)
    (cap : ∀ v,(E G v).card≤d+1)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (dx : d≤G.degree x) (dp : d≤G.degree p) (dq : d≤G.degree q) :
    Fintype.card V≤3*d := by
  by_contra! large
  have dba : G.dist b a=3 := (G.dist_comm (u:=b) (v:=a)).trans dab
  have ab : a≠b := by
    intro h
    rw [h,SimpleGraph.dist_self] at dab
    omega
  have cvs : ∀ w : V,w=b ∨ w=a ∨ w∈X ∨ w∈Y := by
    intro w
    rcases cover w with h|h|h|h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  have swapEnds {v : V} : v=a ∨ v=b ∨ v∈Y → v=b ∨ v=a ∨ v∈Y := by
    rintro (ha|hb|hy)
    · exact .inr (.inl ha)
    · exact .inl hb
    · exact .inr (.inr hy)
  have clX : ∀ u∈X,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈X := by
    intro u hu v e
    rcases cover v with ha|hb|hx|hy
    · exact .inl ha
    · exact .inr (.inl hb)
    · exact .inr (.inr hx)
    · exact (noEdge u hu v hy e).elim
  have clY : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y := by
    intro u hu v e
    rcases cover v with ha|hb|hx|hy
    · exact .inl ha
    · exact .inr (.inl hb)
    · exact (noEdge v hx u hu e.symm).elim
    · exact .inr (.inr hy)
  have clY' : ∀ u∈Y,∀ v,G.Adj u v → v=b ∨ v=a ∨ v∈Y :=
    fun u hu v e=>swapEnds (clY u hu v e)
  obtain ⟨ns,eep,exp,mip,fa,_,fx⟩ :=
    near_tight_slacks hc ap ax dab X Y xX pY bX bY dis cover noEdge x2 p3 noOddP noBadP d
      (cap a) (cap p) (cap x) large
  obtain ⟨_,eeq,exq,miq,fb,_,fz⟩ :=
    near_tight_slacks hc bq bz dba X Y zX qY aX aY dis cvs noEdge z2 q3 noOddQ noBadQ d
      (cap b) (cap q) (cap z) large
  obtain ⟨_,xc⟩ := port_cross_pair hc ap ax X Y xX pY dis cover noEdge
  obtain ⟨_,zc⟩ := port_cross_pair hc bq bz X Y zX qY dis cvs noEdge
  obtain ⟨pc,xp⟩ := tight_shore_even_profile hc ax dab X Y xX bX bY dis x2 xc noBadP exp d fx
  obtain ⟨qc,zp⟩ := tight_shore_even_profile hc bz dba X Y zX aX aY dis z2 zc noBadQ exq d fz
  have pg := tight_remote_gap hc ap dab Y clY eep mip
  have qg := tight_remote_gap hc bq dba Y clY' eeq miq
  obtain ⟨dPQ,Yeq,dM⟩ := tight_shore_partition hc dab Y x2 z2 xc zc (fun w wm=>(pg w wm).1) xp zp
  let M := Mid G Y a b
  have nY : Y.card=2*d-2+M.card := by
    have e := congrArg Finset.card Yeq
    rw [card_union_of_disjoint dM,card_union_of_disjoint dPQ] at e
    change _ = _ + M.card at e
    omega
  have nXY := cut_sum_cards ab X Y aX bX aY bY dis cover
  have hX := degree_near_universal hc ax x2 X aX xX clX
  have msmall : M.card≤1 := by omega
  have ta : Two G Y a⊆M := two_in_mid hc ap dab Y bY clY p3 eep mip z2 zc zp qg
  have tbs := two_in_mid hc bq dba Y aY clY' q3 eeq miq x2 xc xp pg
  have swapM : Mid G Y b a=Mid G Y a b := by
    ext w
    simp only [Mid,mem_filter]
    constructor <;> rintro ⟨wy,e,ev⟩
    · exact ⟨wy,e.symm,by omega⟩
    · exact ⟨wy,e.symm,by omega⟩
  rw [swapM] at tbs
  have ca := degree_port_cap hc ap Y pY clY p3
  have cb := degree_port_cap hc bq Y qY clY' q3
  have disP : Disjoint (Ports G Y a) (Remote G Y a p) := by
    apply disjoint_left.mpr
    intro w wp wr
    have l := SimpleGraph.dist_eq_one_iff_adj.mpr (show w∈Y ∧ G.Adj a w by simpa [Ports] using wp).2
    have h := (mem_filter.mp wr).2.2.2
    omega
  have disQ : Disjoint (Ports G Y b) (Remote G Y b q) := by
    apply disjoint_left.mpr
    intro w wp wr
    have l := SimpleGraph.dist_eq_one_iff_adj.mpr (show w∈Y ∧ G.Adj b w by simpa [Ports] using wp).2
    have h := (mem_filter.mp wr).2.2.2
    omega
  rw [card_union_of_disjoint disP] at pc
  rw [card_union_of_disjoint disQ] at qc
  have tca := card_le_card ta
  have tcb := card_le_card tbs
  have m1 : M.card=1 := by
    change #(Two G Y a)≤M.card at tca
    omega
  have noP : Remote G Y a p=∅ := card_eq_zero.mp (by omega)
  have noQ : Remote G Y b q=∅ := card_eq_zero.mp (by
    change #(Two G Y b)≤M.card at tcb
    omega)
  have exactX : X.card=d := by omega
  obtain ⟨m,me⟩ := card_eq_one.mp m1
  have ml : m∈Two G Y a := by
    have h : (Two G Y a).card=1 := by
      change #(Two G Y a)≤M.card at tca
      have gg : (Remote G Y a p).card=0 := card_eq_zero.mpr noP
      omega
    obtain ⟨v,ve⟩ := card_eq_one.mp h
    have vv : v∈M := ta (by rw [ve]; simp)
    rw [me] at vv
    rw [ve,mem_singleton.mp vv]
    simp
  have am : G.dist a m=2 := (mem_filter.mp ml).2
  have bm : G.dist b m=2 := by
    have mm : m∈M := by rw [me]; simp
    have e := (mem_filter.mp mm).2.1
    omega
  have ea : (Ports G Y a).card+1=d := by simpa [noP] using pc
  have eb : (Ports G Y b).card+1=d := by simpa [noQ] using qc
  have fullY : Y=Ports G Y a∪Ports G Y b∪{m} := by
    rw [noP,noQ,union_empty,union_empty] at Yeq
    exact Yeq.trans (by rw [show Mid G Y a b=M from rfl,me])
  have fullY' : Y=Ports G Y b∪Ports G Y a∪{m} := fullY.trans (by rw [union_comm (Ports G Y a)])
  have ts₁ : Two G Y a⊆{m} := by rw [←me]; exact ta
  have ts₂ : Two G Y b⊆{m} := by rw [←me]; exact tbs
  have fa₂ := near_ports_at_most_two hc dab X Y cover clY fullY ts₁ am bm d eb exactX fa degree
  have fb₂ := near_ports_at_most_two hc dba X Y cvs clY' fullY' ts₂ bm am d ea exactX fb degree
  exact high_count_complement d degree X (Ports G X a) (Ports G X b)
    (by intro w h; exact (show w∈X ∧ G.Adj a w by simpa [Ports] using h).1)
    (by intro w h; exact (show w∈X ∧ G.Adj b w by simpa [Ports] using h).1)
    fa₂ fb₂ exactX dl (fun w wx na nb=>exactX ▸ near_nonport_low X wx na nb clX)

#print axioms conditional_lemma_T
end Graffiti189.AdamEdge
