import DegreeFiveOneFiveGeometry189
import CapSplitRoute189
import WingSignature189



namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private singleton_shore_of_one_port from DegreeFiveOneFourShapes189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem lift_shore_subroute
    {S : Finset V} {A : Finset (↑(↑S : Set V))} {x y : (↑(↑S : Set V))}
    (p : RouteOn (G.induce (↑S : Set V)) A x y) :
    RouteOn G (A.image Subtype.val) x.val y.val := by
  classical
  obtain ⟨p,hp,ps⟩ := p
  let f : (G.induce (↑S : Set V)) →g G := ⟨Subtype.val,id⟩
  refine ⟨p.map f,?_,?_⟩
  · rw [isPath_def,support_map]
    exact hp.support_nodup.map Subtype.val_injective
  intro z
  rw [support_map,List.mem_map,mem_image]
  constructor
  · rintro ⟨v,h,e⟩
    exact ⟨v,(ps v).mp h,e⟩
  rintro ⟨v,h,e⟩
  exact ⟨v,(ps v).mpr h,e⟩

theorem traceable_from_one_five_cap
    (ab : a≠b) {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (five : (cutPorts D).card=5)
    {r : V} (ce : Shore C={r}) (ar : G.Adj a r) (br : G.Adj b r)
    (colors : ∀ c : V,c=a ∨ c=b → 4≤(portColor D c).card)
    (h : Graffiti189Ore.Traceable
      (cap (G.induce (↑(Shore D) : Set V)) (fun u=>u.val∈cutPorts D))) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let S := Shore D
  let U := ↑(↑S : Set V)
  have pos : Nonempty U := by
    obtain ⟨u,up⟩ := card_pos.mp (show 0<(cutPorts D).card by omega)
    exact ⟨⟨u,(mem_filter.mp up).1⟩⟩
  have rc : r∈Shore C := by simp [ce]
  have rOut : r∉S := fun h=>disjoint_left.mp (shore_disjoint cd) rc h
  have an : a∉S := (shore_off D).1
  have bn : b∉S := (shore_off D).2
  have total : ∀ z : V,z∈S ∨ z∈({a,r,b} : Finset V) := by
    intro z
    rcases cover z with e|e|zc|zs
    · exact .inr (by simp [e])
    · exact .inr (by simp [e])
    · exact .inr (by simp [show z=r by simpa [ce] using zc])
    exact .inl zs
  rcases split_of_traceable_cap pos h with ⟨x,y,xP,p⟩|⟨x,y,u,v,A,B,xP,uP,xu,apart,all,p,q⟩
  · have e : (univ : Finset U).image Subtype.val=S := by
      ext z
      exact ⟨fun m=>by obtain ⟨v,_,rfl⟩ := mem_image.mp m; exact v.property,
        fun zs=>mem_image.mpr ⟨⟨z,zs⟩,mem_univ _,rfl⟩⟩
    have free : RouteOn G S x.val y.val := e ▸ lift_shore_subroute p
    have term : WingRealizes G a b (Shore C) .terminal := by
      rw [ce]
      exact ⟨r,r,ar,br,RouteOn.singleton⟩
    have f : WingRealizes G a b (Shore D) .aFree ∨ WingRealizes G a b (Shore D) .bFree :=
      ((mem_filter.mp xP).2).imp (fun h=>⟨x.val,y.val,h,free⟩) (fun h=>⟨x.val,y.val,h,free⟩)
    exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
      an bn cover (.inl ⟨term,f⟩)
  let L := A.image Subtype.val
  let R := B.image Subtype.val
  have lp : RouteOn G L x.val y.val := lift_shore_subroute p
  have rp : RouteOn G R u.val v.val := lift_shore_subroute q
  have lS : L⊆S := by
    intro z h
    obtain ⟨v,_,rfl⟩ := mem_image.mp h
    exact v.property
  have rS : R⊆S := by
    intro z h
    obtain ⟨v,_,rfl⟩ := mem_image.mp h
    exact v.property
  have dis : Disjoint L R := by
    apply disjoint_left.mpr
    intro z zl zr
    obtain ⟨x,xa,ex⟩ := mem_image.mp zl
    obtain ⟨u,ub,eu⟩ := mem_image.mp zr
    have eq : x=u := Subtype.ext (ex.trans eu.symm)
    exact disjoint_left.mp apart xa (eq.symm ▸ ub)
  have eq : L∪R=S := by
    apply Subset.antisymm (union_subset lS rS)
    intro z zs
    let v : U := ⟨z,zs⟩
    have vu : v∈A∪B := all.symm ▸ mem_univ v
    exact (mem_union.mp vu).elim
      (fun m=>mem_union_left _ (mem_image.mpr ⟨v,m,rfl⟩))
      (fun m=>mem_union_right _ (mem_image.mpr ⟨v,m,rfl⟩))
  have no : Disjoint S ({a,r,b} : Finset V) := by
    apply disjoint_left.mpr
    intro z zs h
    simp only [mem_insert,mem_singleton] at h
    exact h.elim (fun e=>an (e ▸ zs)) (fun h=>h.elim (fun e=>rOut (e ▸ zs)) (fun e=>bn (e ▸ zs)))
  have dis1 := no.mono_left lS
  have dis2 : Disjoint (L∪({a,r,b} : Finset V)) R :=
    disjoint_union_left.mpr ⟨dis,no.symm.mono_right rS⟩
  have use {i j : V} (path : RouteOn G ({a,r,b} : Finset V) i j)
      (xi : G.Adj i x.val) (ju : G.Adj j u.val) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    have route := (lp.reverse.join path dis1 xi.symm).join rp dis2 ju
    obtain ⟨p,pp,ps⟩ := route
    refine ⟨y.val,v.val,p,pp,?_⟩
    intro z
    apply (ps z).mpr
    rcases total z with zs|mid
    · have x : z∈L∪R := eq.symm ▸ zs
      exact (mem_union.mp x).elim (fun h=>mem_union_left _ (mem_union_left _ h)) (mem_union_right _)
    exact mem_union_left _ (mem_union_right _ mid)
  have mid := RouteOn.three ar br.symm ab
  rcases one_five_two_distinct_ports_have_opposite_choices five colors xP uP
    (fun h=>xu (Subtype.ext h)) with ⟨ax,bu⟩|⟨bx,au⟩
  · exact use mid ax bu
  exact use mid.reverse bx au

#print axioms traceable_from_one_five_cap
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
