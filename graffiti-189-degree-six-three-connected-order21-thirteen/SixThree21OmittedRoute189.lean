import SixThree21HighOre189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit)
open Graffiti189LongestPath.SixThreeTwenty (HighOmit highOmit_data PortSet mem_portSet)
open private Graffiti189LongestPath.no_endpoints Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem omitted_degree_ge_three (conn : ConnThree G) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) {x : V} (xo : x∉p.support) : 3≤G.degree x := by
  rw [←card_neighborFinset_eq_degree]
  apply Graffiti189LongestPath.boundary_card_of_connectivity 3 conn (x:=x) (a:=a) (A:={x})
  · exact mem_singleton_self _
  · exact fun e=>xo ((mem_singleton.mp e) ▸ p.start_mem_support)
  · exact fun e=>(Graffiti189LongestPath.no_endpoints hp xo).1 ((mem_neighborFinset _ _ _).mp e)
  · apply disjoint_left.mpr
    intro v vm vn
    exact ((mem_neighborFinset _ _ _).mp vn).ne (mem_singleton.mp vm).symm
  · intro v vm w _ e
    exact (mem_neighborFinset _ _ _).mpr ((mem_singleton.mp vm) ▸ e)

theorem omitted_long_route_of_single_pins (conn : ConnThree G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (sz : (Omit p).card=7)
    (single : ∀ z∉p.support,(Pins p z).card≤1)
    {x y : V} (xo : x∉p.support) (yo : y∉p.support) (xy : x≠y) :
    ∃ q : G.Walk x y,q.IsPath ∧ 5≤q.length ∧ ∀ z∈q.support,z∉p.support := by
  classical
  have high (x : V) (xo : x∉p.support) (d : 6≤G.degree x) : x∈HighOmit p :=
    mem_filter.mpr ⟨mem_Omit.mpr xo,d⟩
  have low_high {x y : V} (xo : x∉p.support) (yo : y∉p.support)
      (low : ¬6≤G.degree x) (dy : 6≤G.degree y) :
      ∃ q : G.Walk x y,q.IsPath ∧ 5≤q.length ∧ ∀ z∈q.support,z∉p.support := by
    let A := G.neighborFinset x∩Omit p
    have lower : 2≤A.card := by
      have d := omitted_degree_ge_three conn hp xo
      have b := omitted_inside_degree_lower hp xo
      change G.degree x≤(Pins p x).card+A.card at b
      have s := single x xo
      omega
    obtain ⟨w,wm,wy⟩ : ∃ w∈A,w≠y := by
      by_contra no
      have s : A⊆{y} := fun w wm=>mem_singleton.mpr (by_contra (fun h=>no ⟨w,wm,h⟩))
      have v := card_le_card s
      rw [card_singleton] at v
      omega
    have xw := (mem_neighborFinset _ _ _).mp (mem_inter.mp wm).1
    have wo := mem_Omit.mp (mem_inter.mp wm).2
    have dw := (degree x w xw.ne).resolve_left low
    obtain ⟨q,qp,ql,all⟩ := high_omitted_long_route_of_single_pins degree hp sz single
      (high w wo dw) (high y yo dy) wy
    have xn : x∉q.support := fun m=>low (highOmit_data (all x m)).2
    refine ⟨Walk.cons xw q,qp.cons xn,by simp; omega,?_⟩
    intro z zm
    rcases List.mem_cons.mp zm with rfl|m
    · exact xo
    exact (highOmit_data (all z m)).1
  by_cases dx : 6≤G.degree x
  · by_cases dy : 6≤G.degree y
    · obtain ⟨q,qp,ql,all⟩ := high_omitted_long_route_of_single_pins degree hp sz single
        (high x xo dx) (high y yo dy) xy
      exact ⟨q,qp,ql,fun z zm=>(highOmit_data (all z zm)).1⟩
    obtain ⟨q,qp,ql,all⟩ := low_high yo xo dy dx
    exact ⟨q.reverse,qp.reverse,by simpa using ql,fun z zm=>all z (by simpa using zm)⟩
  exact low_high xo yo dx ((degree x y xy).resolve_left dx)

theorem three_port_sites_of_nonempty_omitted (conn : ConnThree G)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (non : (Omit p).Nonempty) :
    3≤(PortSet p (Omit p)).card := by
  obtain ⟨x,xm⟩ := non
  have ao : a∉Omit p := fun h=>(mem_Omit.mp h) p.start_mem_support
  have ab : a∉PortSet p (Omit p) := by
    intro m
    obtain ⟨_,y,ym,ya⟩ := (mem_portSet hp (fun v vm=>mem_Omit.mp vm)).mp m
    exact (Graffiti189LongestPath.no_endpoints hp (mem_Omit.mp ym)).1 ya
  have dis : Disjoint (Omit p) (PortSet p (Omit p)) := by
    apply disjoint_left.mpr
    intro y ym yp
    exact (mem_Omit.mp ym) ((mem_portSet hp (fun v vm=>mem_Omit.mp vm)).mp yp).1
  exact Graffiti189LongestPath.boundary_card_of_connectivity 3 conn xm ao ab dis
    (fun y ym z zm yz=>(mem_portSet hp (fun v vm=>mem_Omit.mp vm)).mpr
      ⟨Classical.byContradiction (fun h=>zm (mem_Omit.mpr h)),y,ym,yz⟩)

#print axioms omitted_long_route_of_single_pins
#print axioms three_port_sites_of_nonempty_omitted
end Graffiti189LongestPath.SixThreeTwentyOne
