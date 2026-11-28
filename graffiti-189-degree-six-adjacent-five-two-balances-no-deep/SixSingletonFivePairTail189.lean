import SixSingletonFivePairDispatch189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private full_dark_support from SixSingletonFivePairDispatch189
open private shape_two every_balance_dark_hit from SixSingletonFiveSparseCore189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private def vt (side : Bool) : V := if side then a else b
private def vp (side : Bool) : V := if side then x else y

private theorem join_marked_split {L R S : Finset V} (F : ProfileTwo G L R S)
    (side : Bool) {U J : Finset V} (uD : U⊆D) (jD : J⊆D)
    (sep : Disjoint U J) (cover : U∪J=D)
    {h z c t : V} (head : G.Adj (vp side) h) (p : RouteOn G U h z)
    (center : G.Adj z c) (q : RouteOn G (J∪K) c t)
    (exit : t∈K ∨ G.Adj t (vp (!side))) :
    ∃ u v,∃ r : G.Walk u v,r.IsPath ∧ ∀ i,i∈r.support := by
  have port : ∀ u:Bool,G.Adj (vt u) (vp u) := by intro k; cases k; exact F.by'; exact F.ax
  have sing : G.Adj s (vt side) := by cases side; exact F.sb; exact F.sa
  have cport : ∀ c∈K,G.Adj c (vt (!side)) := by
    intro c cm
    cases side
    · exact (F.commonA c cm).symm
    exact (F.commonB c cm).symm
  have termD : ∀ k : Bool,vt k∉D := by decide
  have portD : ∀ k : Bool,vp k∉D := by decide
  have termK : ∀ k : Bool,vt k∉K := by decide
  have portK : ∀ k : Bool,vp k∉K := by decide
  have vtp : ∀ i j : Bool,vt i≠vp j := by decide
  have tNt : ∀ k : Bool,vt k≠vt (!k) := by decide
  have pNp : ∀ k : Bool,vp k≠vp (!k) := by decide
  have sNt : ∀ k : Bool,s≠vt k := by decide
  have sNp : ∀ k : Bool,s≠vp k := by decide
  have p1 := p.prefix head (fun a=>portD _ (uD a))
  have p2 := p1.prefix (port side) (fun m=>(mem_insert.mp m).elim (vtp _ _) (fun h=>termD _ (uD h)))
  have p3 := p2.prefix sing (fun m=>(mem_insert.mp m).elim (sNt _)
    (fun m=>(mem_insert.mp m).elim (sNp _) (fun h=>(by decide : s∉D) (uD h))))
  have offP : vp (!side)∉J∪K := fun m=>(mem_union.mp m).elim (fun j=>portD _ (jD j)) (portK _)
  have offT : vt (!side)∉J∪K := fun m=>(mem_union.mp m).elim (fun j=>termD _ (jD j)) (termK _)
  have sepAll : Disjoint (insert s (insert (vt side) (insert (vp side) U)))
      (insert (vt (!side)) (insert (vp (!side)) (J∪K))) := by
    apply disjoint_left.mpr
    intro u um un
    simp only [mem_insert,mem_union] at um un
    rcases um with rfl|rfl|rfl|um
    · exact un.elim (sNt _) (fun h=>h.elim (sNp _) (fun h=>h.elim
        (fun m=>(by decide : s∉D) (jD m)) (by decide : s∉K)))
    · exact un.elim (tNt _) (fun h=>h.elim (vtp _ _) (fun h=>h.elim
        (fun m=>termD _ (jD m)) (termK _)))
    · exact un.elim (Ne.symm (vtp _ _)) (fun h=>h.elim (pNp _) (fun h=>h.elim
        (fun m=>portD _ (jD m)) (portK _)))
    have u' := uD um
    rcases un with rfl|rfl|uJ|uK
    · exact termD _ u'
    · exact portD _ u'
    · exact disjoint_left.mp sep um uJ
    exact disjoint_left.mp (by decide : Disjoint K D) uK u'
  have allV : ∀ u : V,u∈insert s (insert (vt side) (insert (vp side) U)) ∪
      insert (vt (!side)) (insert (vp (!side)) (J∪K)) := by
    intro u
    have lem : ∀ (side : Bool) (u : V),u=s ∨ u=vt side ∨ u=vp side ∨
        u=vt (!side) ∨ u=vp (!side) ∨ u∈K ∨ u∈D := by decide
    have h := lem side u
    rw [←cover,mem_union] at h
    simp only [mem_insert,mem_union]
    tauto
  rcases exit with tK|tp
  · have q1 := q.suffix (cport t tK) offT
    have q2 := q1.suffix (port (!side)) (fun m=>(mem_insert.mp m).elim (Ne.symm (vtp _ _)) offP)
    rw [insert_comm (vp (!side)) (vt (!side))] at q2
    obtain ⟨r,rp,rs⟩ := p3.join q2 sepAll center
    exact ⟨s,vp (!side),r,rp,fun i=>(rs i).mpr (allV i)⟩
  have q1 := q.suffix tp offP
  have q2 := q1.suffix (port (!side)).symm (fun m=>(mem_insert.mp m).elim (vtp _ _) offT)
  obtain ⟨r,rp,rs⟩ := p3.join q2 sepAll center
  exact ⟨s,vt (!side),r,rp,fun i=>(rs i).mpr (allV i)⟩

theorem traceable_nonadjacent_two_low {L R S : Finset V} (F : ProfileTwo G L R S)
    {z w : V} (zm : z∈D\S) (wm : w∈D\S) (zw : z≠w)
    (nozw : ¬G.Adj z w) (lz : (inside G D z).card≤3) (lw : (inside G D w).card≤3)
    (noBoth : ∀ c∈K,¬(G.Adj c x ∧ G.Adj c y)) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  have sh := (shape_two F zm wm zw).1
  obtain ⟨n,nm,nz⟩ := every_balance_dark_hit F (mem_sdiff.mp zm).1
  have ns : n∈S := by
    by_contra no
    have h : n∈D\S := mem_sdiff.mpr ⟨nm,no⟩
    rw [sh,mem_insert,mem_singleton] at h
    exact h.elim nz.ne (fun h=>nozw (h ▸ nz.symm))
  obtain ⟨h,hm,core⟩ := root_through_strict_core F zm wm zw ns
  have p := core.suffix nz (mem_sdiff.mp zm).2
  have uD : insert z S⊆D := insert_subset (mem_sdiff.mp zm).1 F.core_sub
  have jD : ({w}:Finset V)⊆D := singleton_subset_iff.mpr (mem_sdiff.mp wm).1
  have sep : Disjoint (insert z S) ({w}:Finset V) := by
    apply disjoint_left.mpr
    intro i im iw
    rw [mem_singleton] at iw
    subst i
    exact (mem_insert.mp im).elim zw.symm (mem_sdiff.mp wm).2
  have cv : insert z S∪({w}:Finset V)=D := by
    rw [←full_dark_support F zm wm zw]
    ext i
    simp only [mem_union,mem_insert,mem_singleton]
    tauto
  have unionK : ({w}:Finset V)∪K=insert w K := by
    ext v
    simp only [mem_union,mem_singleton,mem_insert]
  have go (side : Bool) (edge : G.Adj (vp side) h) :
      ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
    have tag : vp (!side)=x ∨ vp (!side)=y := by cases side; exact .inl rfl; exact .inr rfl
    obtain ⟨c,_,zc,sol⟩ := interleaved_common_plan F zm wm zw tag lz lw noBoth
    rcases sol with ⟨t,tm,q⟩ | ⟨q,e⟩
    · apply join_marked_split F side uD jD sep cv edge p zc _ (.inl tm)
      simpa only [unionK] using q
    apply join_marked_split F side uD jD sep cv edge p zc _ (.inr e)
    simpa only [unionK] using q
  rcases mem_union.mp hm with hL|hR
  · exact go true (F.xL h hL)
  exact go false (F.yR h hR)

#print axioms traceable_nonadjacent_two_low
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
