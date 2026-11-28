import EJEndpointMarks189
import DegreeFiveRouteBasic189

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath.CrossSaturation
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- A path with a universal first vertex can be rerooted at every
vertex of its support, without changing that support. -/
theorem route_from_hub_path {h t x : V} (p : G.Walk h t) (hp : p.IsPath)
    (hub : ∀ v,v∈p.support → v≠h → G.Adj h v) (xm : x∈p.support) :
    ∃ y,∃ q : G.Walk x y,q.IsPath ∧ ∀ z,z∈q.support ↔ z∈p.support := by
  classical
  obtain ⟨l,r,eq⟩ := mem_support_iff_exists_append.mp xm
  cases r with
  | nil =>
    exact ⟨h,p.reverse,hp.reverse,by intro z; simp⟩
  | @cons _ v _ xv r =>
    have old : p.support=l.support++r.support := by
      rw [eq]
      simp only [support_append,support_cons,List.tail_cons]
    have nd := List.nodup_append.mp (old ▸ hp.support_nodup)
    have vv : v∈r.support := r.start_mem_support
    have vh : v≠h := fun eq=>nd.2.2 l.start_mem_support (eq ▸ vv)
    have hv := hub v (old.symm ▸ List.mem_append_right _ vv) vh
    let q := l.reverse.append (.cons hv r)
    have ss : q.support=l.support.reverse++r.support := by
      simp only [q,support_append,support_cons,List.tail_cons,support_reverse]
    refine ⟨_,q,Walk.IsPath.mk' ?_,?_⟩
    · rw [ss,List.nodup_append]
      exact ⟨List.nodup_reverse.mpr nd.1,nd.2.1,
        fun _ zl zr=>nd.2.2 (List.mem_reverse.mp zl) zr⟩
    intro z
    simp [ss,old]

theorem traceable_of_two_hub_paths (hc : G.Connected)
    {x y z w : V} (p : G.Walk x y) (q : G.Walk z w)
    (hp : p.IsPath) (hq : q.IsPath)
    (lh : ∀ t,t∈p.support → t≠x → G.Adj x t)
    (rh : ∀ t,t∈q.support → t≠z → G.Adj z t)
    (dis : List.Disjoint p.support q.support)
    (cover : ∀ t,t∈p.support ∨ t∈q.support) :
    Traceable G := by
  classical
  have hit : ∃ a∈p.support,∃ b∈q.support,G.Adj a b := by
    apply Classical.byContradiction
    intro no
    have stay {u v : V} (r : G.Walk u v) : u∈p.support → v∈p.support := by
      induction r with
      | nil => exact id
      | @cons u t v ut r ih =>
        intro h
        exact ih ((cover t).elim id (fun h'=> (no ⟨u,h,t,h',ut⟩).elim))
    obtain ⟨r⟩ := hc.preconnected x z
    exact dis (stay r p.start_mem_support) q.start_mem_support
  obtain ⟨a,am,b,bm,ab⟩ := hit
  obtain ⟨u,left,lp,ls⟩ := route_from_hub_path p hp lh am
  obtain ⟨v,right,rp,rs⟩ := route_from_hub_path q hq rh bm
  let A := p.support.toFinset
  let B := q.support.toFinset
  have l : RouteOn G A a u := ⟨left,lp,fun t=>by simp only [A,List.mem_toFinset,ls]⟩
  have r : RouteOn G B b v := ⟨right,rp,fun t=>by simp only [B,List.mem_toFinset,rs]⟩
  have sep : Disjoint A B := disjoint_left.mpr (fun t ta tb=>dis (List.mem_toFinset.mp ta) (List.mem_toFinset.mp tb))
  obtain ⟨walk,path,all⟩ := l.reverse.join r sep ab
  exact ⟨u,v,walk,path,fun t=>(all t).mpr
    (mem_union.mpr ((cover t).imp List.mem_toFinset.mpr List.mem_toFinset.mpr))⟩

#print axioms traceable_of_two_hub_paths
end Graffiti189Ore
