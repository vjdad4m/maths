import DegreeFiveSmallSides189
import ArticulationClique189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

def RouteOn (G : SimpleGraph V) (A : Finset V) (x y : V) : Prop :=
  ∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support ↔ z∈A

theorem RouteOn.reverse {A : Finset V} {x y : V} (p : RouteOn G A x y) :
    RouteOn G A y x := by
  obtain ⟨q,qp,qs⟩ := p
  exact ⟨q.reverse,qp.reverse,fun z=>by simpa using qs z⟩

theorem RouteOn.edge {x y : V} (xy : G.Adj x y) : RouteOn G {x,y} x y := by
  have h : (Walk.cons xy (.nil : G.Walk y y)).IsPath := IsPath.cons (by simp) (by simpa using xy.ne)
  exact ⟨.cons xy .nil,h,by intro z; simp [support_cons]⟩

theorem RouteOn.singleton {x : V} : RouteOn G {x} x x :=
  ⟨.nil,by simp,by intro z; simp⟩

theorem RouteOn.three {x y z : V} (xy : G.Adj x y) (yz : G.Adj y z) (xz : x≠z) :
    RouteOn G {x,y,z} x z := by
  obtain ⟨q,h,s⟩ := RouteOn.edge yz
  have off : x∉q.support := fun h=>by
    have v := (s x).mp h
    simp [xy.ne,xz] at v
  exact ⟨.cons xy q,h.cons off,by intro w; simp only [support_cons,List.mem_cons,mem_insert,s]⟩

theorem RouteOn.join {A B : Finset V} {x y z t : V}
    (p : RouteOn G A x y) (q : RouteOn G B z t)
    (disj : Disjoint A B) (edge : G.Adj y z) : RouteOn G (A∪B) x t := by
  obtain ⟨l,lp,ls⟩ := p
  obtain ⟨r,rp,rs⟩ := q
  refine ⟨l.append (.cons edge r),?_,?_⟩
  · rw [isPath_def,support_append,List.nodup_append,support_cons,List.tail_cons]
    exact ⟨lp.support_nodup,rp.support_nodup,fun v vl vr=>disjoint_left.mp disj ((ls _).mp vl) ((rs _).mp vr)⟩
  intro v
  rw [mem_support_append_iff,mem_union]
  simp only [support_cons,List.mem_cons,ls,rs]
  have m : y∈A := (ls _).mp l.end_mem_support
  constructor
  · rintro (vA|rfl|vB)
    · exact Or.inl vA
    · exact Or.inl m
    exact Or.inr vB
  · exact fun h=>h.imp id Or.inr

theorem RouteOn.prefix {A : Finset V} {x y z : V}
    (p : RouteOn G A y z) (xy : G.Adj x y) (off : x∉A) : RouteOn G (insert x A) x z := by
  obtain ⟨q,qp,qs⟩ := p
  exact ⟨.cons xy q,qp.cons (fun h=>off ((qs _).mp h)),by intro u; simp only [support_cons,List.mem_cons,mem_insert,qs]⟩

theorem RouteOn.suffix {A : Finset V} {x y z : V}
    (p : RouteOn G A x y) (yz : G.Adj y z) (off : z∉A) : RouteOn G (insert z A) x z := by
  obtain ⟨q,qp,qs⟩ := p
  refine ⟨q.concat yz,path_concat_new q qp yz (fun h=>off ((qs _).mp h)),?_⟩
  intro u
  simp only [support_concat,List.concat_eq_append,List.mem_append,qs,List.mem_singleton,mem_insert,or_comm]

/-- A path of all nonporters joins complete port classes when it has an
available first port and an available last port. -/
theorem route_join_cliques {A B I : Finset V} (aC : CompleteOn G A) (bC : CompleteOn G B)
    (ab : Disjoint A B) (ai : Disjoint A I) (bi : Disjoint B I)
    {x u v y : V} (xA : x∈A) (yB : y∈B)
    (xu : G.Adj x u) (vy : G.Adj v y) (r : RouteOn G I u v) :
    ∃ p∈A,∃ q∈B,RouteOn G ((A∪I)∪B) p q := by
  obtain ⟨p,pa,pp,ps⟩ := rooted_path_in_clique A aC xA
  obtain ⟨q,qb,qp,qs⟩ := rooted_path_in_clique B bC yB
  have ra : RouteOn G A x p := ⟨pa,pp,ps⟩
  have rb : RouteOn G B y q := ⟨qb,qp,qs⟩
  have r1 := ra.reverse.join r ai xu
  have r2 := r1.join rb (disjoint_union_left.mpr ⟨ab,bi.symm⟩) vy
  exact ⟨p,(ps p).mp pa.end_mem_support,q,(qs q).mp qb.end_mem_support,r2⟩

theorem two_high_points {A : Finset V} (a3 : A.card=3)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y) :
    ∃ x∈A,∃ y∈A,x≠y ∧ 5≤G.degree x ∧ 5≤G.degree y := by
  obtain ⟨x,y,z,xy,xz,yz,eq⟩ := card_eq_three.mp a3
  have xm : x∈A := by simp [eq]
  have ym : y∈A := by simp [eq]
  have zm : z∈A := by simp [eq]
  by_cases hx : 5≤G.degree x
  · rcases degree y z yz with p|p
    · exact ⟨x,xm,y,ym,xy,hx,p⟩
    exact ⟨x,xm,z,zm,xz,hx,p⟩
  exact ⟨y,ym,z,zm,yz,(degree x y xy).resolve_left hx,(degree x z xz).resolve_left hx⟩

#print axioms RouteOn.join
#print axioms route_join_cliques
#print axioms two_high_points
end Graffiti189LongestPath.CrossSaturation
