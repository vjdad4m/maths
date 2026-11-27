import DegreeFiveBothFiveResidual189
import TerminalOreClosure189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_connected from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Five all-port vertices and at least one shared porter suffice for a
terminal route, even without universal common vertices. -/
theorem terminal_mask_of_five_vertex_all_port_shore
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (five : (cutPorts C).card=5) (size : (Shore C).card=5)
    {x : V} (xs : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset U := univ.filter (fun u=>5≤G.degree u.val)
  let H := completeWith J A
  letI : DecidableRel H.Adj := Classical.decRel _
  have allP : cutPorts C=S := eq_of_subset_of_card_le (filter_subset _ _) (by
    rw [five]; exact size.le)
  have port (u : V) (us : u∈S) : G.Adj a u ∨ G.Adj b u :=
    (cut_mem_iff.mp (allP.symm ▸ us)).2
  have cl : CompleteOn H A := completeWith_of_mem J A
  have sizeU : Fintype.card U=5 := (Fintype.card_coe S).trans size
  have hs (u : U) : u∈A ↔ 5≤G.degree u.val := by simp [A]
  have lower (u : U) (ua : u∈A) : 3≤J.degree u := by
    change 3≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    exact inside_high_at_least_three u.property ((hs u).mp ua)
  have cap (u v : U) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at uv
    obtain ⟨ua,va,_⟩ := uv.resolve_left no
    have hl := lower u ua
    have hr := lower v va
    omega
  have pull {u v : U} (p : RouteOn H univ u v) : RouteOn G S u.val v.val := by
    obtain ⟨r,rp,rs⟩ := p
    obtain ⟨q,qp,qs⟩ := terminal_ore_closure (completeWith_mono J A) cap r rp
      (fun w=>(rs _).mpr (mem_univ _))
    exact lift_side_path S q qp qs
  have pick (u v : V) : ∃ w∈S,w≠u ∧ w≠v := by
    have out : ¬S⊆({u,v} : Finset V) := by
      intro sub
      have k := card_le_card sub
      have t := card_insert_le u ({v} : Finset V)
      rw [card_singleton] at t
      have count : S.card=5 := size
      omega
    obtain ⟨w,ws,no⟩ := not_subset.mp out
    exact ⟨w,ws,fun e=>no (by simp [e]),fun e=>no (by simp [e])⟩
  by_cases low : ∃ z∈S,¬5≤G.degree z
  · obtain ⟨z,zs,zLow⟩ := low
    let zz : U := ⟨z,zs⟩
    have zaEq : A=univ.erase zz := by
      ext u
      rw [hs]
      by_cases uz : u=zz
      · subst u; simp [zz,zLow]
      have u5 := (degree u.val z (fun e=>uz (Subtype.ext e))).resolve_right zLow
      simp [uz,u5]
    have neighbors : ∃ w∈S,G.Adj z w := by
      obtain ⟨v,vs,vz,_⟩ := pick z z
      obtain ⟨p⟩ := (shore_connected C).preconnected zz ⟨v,vs⟩
      have start {s t : U} (q : J.Walk s t) (e : s≠t) : ∃ w,J.Adj s w := by
        cases q with
        | nil => exact (e rfl).elim
        | cons h _ => exact ⟨_,h⟩
      obtain ⟨w,h⟩ := start p (fun e=>vz (congrArg Subtype.val e).symm)
      exact ⟨w.val,w.property,h⟩
    obtain ⟨w,ws,zw⟩ := neighbors
    have away {v : V} (vs : v∈S) (zv : G.Adj z v) {t : V} (ts : t∈S)
        (tz : t≠z) (vt : v≠t) : RouteOn G S z t := by
      let vv : U := ⟨v,vs⟩
      let tt : U := ⟨t,ts⟩
      have va : vv∈A := by
        rw [zaEq]
        exact mem_erase.mpr ⟨fun e=>zv.ne.symm (congrArg Subtype.val e),mem_univ _⟩
      have ta : tt∈A := by
        rw [zaEq]
        exact mem_erase.mpr ⟨fun e=>tz (congrArg Subtype.val e),mem_univ _⟩
      obtain ⟨p,pp,ps⟩ := path_between_in_clique A cl va ta (fun e=>vt (congrArg Subtype.val e))
      have path : RouteOn H A vv tt := ⟨p,pp,ps⟩
      have edge : H.Adj zz vv := (completeWith_mono J A) zv
      have off : zz∉A := by simp [zaEq]
      have eq : insert zz A=univ := by rw [zaEq,insert_erase (mem_univ _)]
      exact pull (eq ▸ path.prefix edge off)
    by_cases both : G.Adj a z ∧ G.Adj b z
    · obtain ⟨t,ts,tz,tw⟩ := pick z w
      have route := away ws zw ts tz tw.symm
      rcases port t ts with at'|bt
      · exact ⟨t,z,at',both.2,route.reverse⟩
      exact ⟨z,t,both.1,bt,route⟩
    have get (d : V) (which : d=a ∨ d=b) (dx : G.Adj d x) (nz : ¬G.Adj d z) :
        ∃ t, G.Adj d t ∧ RouteOn G S z t := by
      by_cases alternate : ∃ t∈S,G.Adj d t ∧ t≠w
      · obtain ⟨t,ts,dt,tw⟩ := alternate
        have tz : t≠z := fun e=>nz (e ▸ dt)
        exact ⟨t,dt,away ws zw ts tz tw.symm⟩
      have wx : w=x := by
        apply Classical.byContradiction
        intro n
        exact alternate ⟨x,xs,dx,fun e=>n e.symm⟩
      obtain ⟨v,vs,vz,vw⟩ := pick z w
      have nd : ¬G.Adj d v := fun dv=>alternate ⟨v,vs,dv,vw⟩
      have nc : ¬(G.Adj a v ∧ G.Adj b v) := fun h=>
        nd (which.elim (fun p=>p.symm ▸ h.1) (fun p=>p.symm ▸ h.2))
      have v5 := (degree v z vz).resolve_right zLow
      have card : 4≤(inside G S v).card := inside_high_at_least_four_if_exclusive vs v5 nc
      have sub : inside G S v⊆S.erase v := by
        intro u um
        obtain ⟨us,vu⟩ := mem_filter.mp um
        exact mem_erase.mpr ⟨vu.ne.symm,us⟩
      have eq : inside G S v=S.erase v := eq_of_subset_of_card_le sub (by
        rw [card_erase_of_mem vs]
        have k : S.card=5 := size
        omega)
      have vz' : G.Adj v z := (mem_filter.mp (show z∈inside G S v by
        rw [eq]; exact mem_erase.mpr ⟨vz.symm,zs⟩)).2
      exact ⟨w,wx.symm ▸ dx,away vs vz'.symm ws zw.ne.symm vw⟩
    rcases port z zs with az|bz
    · obtain ⟨t,bt,path⟩ := get b (.inr rfl) bx (fun bz=>both ⟨az,bz⟩)
      exact ⟨z,t,az,bt,path⟩
    obtain ⟨t,at',path⟩ := get a (.inl rfl) ax (fun az=>both ⟨az,bz⟩)
    exact ⟨t,z,at',bz,path.reverse⟩
  have aU : A=(univ : Finset U) := by
    ext u
    have h : 5≤G.degree u.val := Classical.byContradiction (fun n=>low ⟨u.val,u.property,n⟩)
    simp [hs,h]
  obtain ⟨v,vs,vx,_⟩ := pick x x
  let xx : U := ⟨x,xs⟩
  let vv : U := ⟨v,vs⟩
  have xa : xx∈A := by simp [aU]
  have va : vv∈A := by simp [aU]
  obtain ⟨p,pp,ps⟩ := path_between_in_clique A cl xa va (fun h=>vx (congrArg Subtype.val h).symm)
  have q : RouteOn H univ xx vv := aU ▸ (show RouteOn H A xx vv from ⟨p,pp,ps⟩)
  have r := pull q
  rcases port v vs with av|bv
  · exact ⟨v,x,av,bx,r.reverse⟩
  exact ⟨x,v,ax,bv,r⟩

#print axioms terminal_mask_of_five_vertex_all_port_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
