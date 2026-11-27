import DegreeFiveActualCut189
import DegreeFiveRouteBasic189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveLonelyPortGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private lonely_opposite_high_and_common_size_four from DegreeFiveExclusiveGateway189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem common_four_is_clique
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (four : (Shore C).card=4) :
    CompleteOn G (Shore C) := by
  classical
  have upper {u v : V} (uC : u∈Shore C) (vC : v∈Shore C) (uv : u≠v)
      (no : ¬G.Adj u v) : ¬5≤G.degree u := by
    have sub : G.neighborFinset u⊆insert a (insert b (((Shore C).erase u).erase v)) := by
      intro z hz
      have az := (mem_neighborFinset G u z).mp hz
      rcases shore_closed C u uC z az with rfl|rfl|zC
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _)
      have zv : z≠v := fun e=>no (e ▸ az)
      exact mem_insert_of_mem (mem_insert_of_mem
        (mem_erase.mpr ⟨zv,mem_erase.mpr ⟨az.ne.symm,zC⟩⟩))
    have va : v∈(Shore C).erase u := mem_erase.mpr ⟨uv.symm,vC⟩
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree] at h
    have ca := card_insert_le a (insert b (((Shore C).erase u).erase v))
    have cb := card_insert_le b (((Shore C).erase u).erase v)
    rw [card_erase_of_mem va,card_erase_of_mem uC,four] at cb
    omega
  intro u uC v vC uv
  apply Classical.byContradiction
  intro e
  exact (degree u v uv).elim (upper uC vC uv e)
    (upper vC uC uv.symm (fun h=>e h.symm))

private theorem two_high_members_of_four
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {A : Finset V} (four : A.card=4) :
    ∃ u∈A,∃ v∈A,u≠v ∧ 5≤G.degree u ∧ 5≤G.degree v := by
  classical
  let H := A.filter (fun u=>5≤G.degree u)
  have lo : (A.filter (fun u=>¬5≤G.degree u)).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    apply Classical.byContradiction
    intro ne
    exact (degree u v ne).elim (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have eq := filter_card_add_filter_neg_card_eq_card (s:=A) (fun u=>5≤G.degree u)
  change H.card+_=A.card at eq
  obtain ⟨u,uh,v,vh,ne⟩ := one_lt_card.mp (show 1<H.card by omega)
  exact ⟨u,(mem_filter.mp uh).1,v,(mem_filter.mp vh).1,ne,(mem_filter.mp uh).2,(mem_filter.mp vh).2⟩

private theorem equal_nbr_sets_of_both_high_overlap
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {A B : Finset V} (eq : A.card=B.card)
    (ab : ∀ u∈A,5≤G.degree u → u∈B)
    (ba : ∀ u∈B,5≤G.degree u → u∈A) : A=B := by
  classical
  apply Classical.byContradiction
  intro ne
  have x : ∃ x∈A,x∉B := by
    apply Classical.byContradiction
    intro no
    apply ne
    exact eq_of_subset_of_card_le (fun u h=>Classical.byContradiction (fun h'=>no ⟨u,h,h'⟩)) eq.ge
  have y : ∃ y∈B,y∉A := by
    apply Classical.byContradiction
    intro no
    apply ne
    symm
    exact eq_of_subset_of_card_le (fun u h=>Classical.byContradiction (fun h'=>no ⟨u,h,h'⟩)) eq.le
  obtain ⟨x,xa,xb⟩ := x
  obtain ⟨y,yb,ya⟩ := y
  have xy : x≠y := fun e=>xb (e.symm ▸ yb)
  exact (degree x y xy).elim (fun h=>xb (ab x xa h)) (fun h=>ya (ba y yb h))

private theorem no_common_right_two_port_geometry
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {u v : V} (uD : u∈Shore D) (vD : v∈Shore D)
    (au : G.Adj a u) (bv : G.Adj b v) (bu : ¬G.Adj b u) (av : ¬G.Adj a v)
    (u5 : 5≤G.degree u) (v5 : 5≤G.degree v)
    (a1 : (portColor D a).card=1) (b1 : (portColor D b).card=1)
    (a4 : (portColor C a).card=4) (b4 : (portColor C b).card=4)
    (p2 : (cutPorts D).card=2) :
    ∃ N : Finset V, N.card=4 ∧ CompleteOn G N ∧
      u∉N ∧ v∉N ∧ u≠v ∧ ¬G.Adj u v ∧
      (∀ w∈N, G.Adj u w ∧ G.Adj v w) ∧ Shore D=insert u (insert v N) := by
  classical
  let Nu := inside G (Shore D) u
  let Nv := inside G (Shore D) v
  obtain ⟨p,pD,nu,pEq,uno,uNear,uFar⟩ := lonely_high_port_geometry hc two even degree cd
    (.inl ⟨rfl,rfl⟩) uD au bu u5 a1 a4 (by omega)
  obtain ⟨q,qD,nv,qEq,vno,vNear,vFar⟩ := lonely_high_port_geometry hc two even degree cd
    (.inr ⟨rfl,rfl⟩) vD bv av v5 b1 b4 (by omega)
  change Nu.card=4 at nu
  change Nv.card=4 at nv
  have uv : u≠v := fun e=>bu (e.symm ▸ bv)
  have noUV := uno v vD bv
  have vp : v=p := by
    apply Classical.byContradiction
    intro nv
    have pv := uFar v vD uv.symm noUV nv
    have charge (t : V) (tN : t∈Nu) (t5 : 5≤G.degree t) : t∈secondShore D v := by
      obtain ⟨tl,ut⟩ := mem_filter.mp tN
      have nt : ¬G.Adj v t := by
        intro vt
        have uv2 := d2 hc uv noUV ut vt.symm
        have hv : v∈secondShore D u := mem_inter.mpr ⟨vD,uv2⟩
        exact nv (by simpa [pEq] using hv)
      have vt : v≠t := fun e=>noUV (e.symm ▸ ut)
      exact mem_inter.mpr ⟨tl,d2 hc vt nt pv.symm (uNear t tN t5).1.symm⟩
    obtain ⟨s,ss,t,ts,ne,sh,th⟩ := two_high_members_of_four degree nu
    have sq : s=q := by simpa [qEq] using charge s ss sh
    have tq : t=q := by simpa [qEq] using charge t ts th
    exact ne (sq.trans tq.symm)
  have vu2 : u∈secondShore D v := by
    have hv : v∈secondShore D u := by simp [pEq,vp]
    have h : G.dist u v=2 := by simpa [DistanceTwo] using (mem_inter.mp hv).2
    have rev : G.dist v u=2 := by rwa [SimpleGraph.dist_comm]
    exact mem_inter.mpr ⟨uD,by simp [DistanceTwo,rev]⟩
  have uq : u=q := by simpa [qEq] using vu2
  have same : Nu=Nv := equal_nbr_sets_of_both_high_overlap degree (nu.trans nv.symm)
    (fun w wn h=>mem_filter.mpr ⟨(mem_filter.mp wn).1,vp ▸ (uNear w wn h).1.symm⟩)
    (fun w wn h=>mem_filter.mpr ⟨(mem_filter.mp wn).1,uq ▸ (vNear w wn h).1.symm⟩)
  have uOff : u∉Nu := fun h=>G.loopless _ (mem_filter.mp h).2
  have vOff : v∉Nu := fun h=>noUV (mem_filter.mp h).2
  have eqD : Shore D=insert u (insert v Nu) := by
    ext z
    constructor
    · intro zd
      by_cases zu : z=u
      · exact mem_insert.mpr (.inl zu)
      by_cases zv : z=v
      · exact mem_insert_of_mem (mem_insert.mpr (.inl zv))
      by_cases uz : G.Adj u z
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨zd,uz⟩))
      have pz := uFar z zd zu uz (fun e=>zv (e.trans vp.symm))
      have vN : z∈Nv := mem_filter.mpr ⟨zd,vp ▸ pz⟩
      exact mem_insert_of_mem (mem_insert_of_mem (same.symm ▸ vN))
    intro h
    rcases mem_insert.mp h with rfl|h
    · exact uD
    rcases mem_insert.mp h with rfl|h
    · exact vD
    exact (mem_filter.mp h).1
  have clique : CompleteOn G Nu := by
    intro x hx y hy ne
    rcases degree x y ne with xh|yh
    · exact (uNear x hx xh).2 y hy ne.symm
    exact ((uNear y hy yh).2 x hx ne).symm
  refine ⟨Nu,nu,clique,uOff,vOff,uv,noUV,?_,eqD⟩
  intro w wn
  exact ⟨(mem_filter.mp wn).2,(mem_filter.mp (same ▸ wn)).2⟩

/-- Exact p=2 branch: the contact component is a K6 with only the
contact-to-contact edge absent, and the common side is K4. -/
theorem traceable_of_two_exclusive_foreign_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (p2 : (cutPorts D).card=2) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have hA := shore_hit_a ab conn D
  have hB := shore_hit_b ab conn D
  let T : Split G a b :=
    ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,shore_connected D,
      (fun u ud v vc e=>by
        rcases shore_closed D u ud v e with rfl|rfl|vD
        · exact (shore_off C).1 vc
        · exact (shore_off C).2 vc
        exact disjoint_left.mp (shore_disjoint cd) vc vD),
      hA,hB,(fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  obtain ⟨u,uD,au⟩ := hA
  obtain ⟨v,vD,bv⟩ := hB
  have bu : ¬G.Adj b u := fun e=>none _ uD ⟨au,e⟩
  have av : ¬G.Adj a v := fun e=>none _ vD ⟨e,bv⟩
  let P := portColor D a
  let Q := portColor D b
  have posP := card_pos.mpr (show P.Nonempty from ⟨u,mem_filter.mpr ⟨uD,au⟩⟩)
  have posQ := card_pos.mpr (show Q.Nonempty from ⟨v,mem_filter.mpr ⟨vD,bv⟩⟩)
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z zp zq
    exact none _ (mem_filter.mp zp).1 ⟨(mem_filter.mp zp).2,(mem_filter.mp zq).2⟩
  have union : P∪Q=cutPorts D := by
    ext z
    change z∈(Shore D).filter (G.Adj a)∪(Shore D).filter (G.Adj b) ↔
      z∈(Shore D).filter (fun z=>G.Adj a z ∨ G.Adj b z)
    simp [and_or_left]
  have cnt := congrArg Finset.card union
  rw [card_union_of_disjoint dis] at cnt
  have a1 : (portColor D a).card=1 := by change P.card=1; omega
  have b1 : (portColor D b).card=1 := by change Q.card=1; omega
  have ac := opposite_ports_at_exclusive_le_four T hc even uD au bu
  have bc := opposite_ports_at_exclusive_le_four T.flip hc even vD bv av
  change (portColor C a).card≤4 at ac
  change (portColor C b).card≤4 at bc
  obtain ⟨u5,a4,c4⟩ := lonely_opposite_high_and_common_size_four hc two even degree cd cover
    (.inl ⟨rfl,rfl⟩) xC ax uD au bu vD bv av a1 ac
  obtain ⟨v5,b4,_⟩ := lonely_opposite_high_and_common_size_four hc two even degree cd cover
    (.inr ⟨rfl,rfl⟩) xC bx vD bv av uD au bu b1 bc
  have allB : ∀ z∈Shore C,G.Adj b z := by
    have sub : portColor C b⊆Shore C := filter_subset _ _
    have eq := eq_of_subset_of_card_le sub (by omega)
    intro z zC
    exact (mem_filter.mp (eq.symm ▸ zC)).2
  obtain ⟨N,N4,clique,uOff,vOff,uv,noUV,adj,eqD⟩ := no_common_right_two_port_geometry hc two
    even degree cd uD vD au bv bu av u5 v5 a1 b1 a4 b4 p2
  obtain ⟨k,kN⟩ := card_pos.mp (show 0<N.card by omega)
  obtain ⟨l,p,pp,ps⟩ := rooted_path_in_clique N clique kN
  have lN := (ps _).mp p.end_mem_support
  have wing : RouteOn G (Shore D) u v := by
    have r : RouteOn G N k l := ⟨p,pp,ps⟩
    have r' := r.prefix (adj k kN).1 uOff
    have result := r'.suffix (adj l lN).2.symm
      (fun h=>(mem_insert.mp h).elim uv.symm vOff)
    rw [insert_comm,←eqD] at result
    exact result
  obtain ⟨j,p,pp,ps⟩ := rooted_path_in_clique (Shore C) (common_four_is_clique degree c4) xC
  have jC := (ps _).mp p.end_mem_support
  have other : RouteOn G (insert b (insert a (Shore C))) a b := by
    have r : RouteOn G (Shore C) x j := ⟨p,pp,ps⟩
    have rr := r.prefix ax (shore_off C).1
    exact rr.suffix (allB j jC).symm (fun h=>(mem_insert.mp h).elim ab.symm (shore_off C).2)
  have joinDis : Disjoint (Shore D) (insert b (insert a (Shore C))) := by
    apply disjoint_left.mpr
    intro z zd zr
    rcases mem_insert.mp zr with rfl|zr
    · exact (shore_off D).2 zd
    rcases mem_insert.mp zr with rfl|zr
    · exact (shore_off D).1 zd
    exact disjoint_left.mp (shore_disjoint cd) zr zd
  obtain ⟨p,pp,ps⟩ := wing.reverse.join other joinDis au.symm
  refine ⟨v,b,p,pp,fun z=>(ps z).mpr ?_⟩
  rcases cover z with rfl|rfl|zc|zd
  · simp
  · simp
  · exact mem_union_right _ (mem_insert_of_mem (mem_insert_of_mem zc))
  exact mem_union_left _ zd

#print axioms traceable_of_two_exclusive_foreign_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
