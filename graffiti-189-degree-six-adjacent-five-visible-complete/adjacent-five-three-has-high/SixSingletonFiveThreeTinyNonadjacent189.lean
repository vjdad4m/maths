import SixSingletonFiveThreeTinyTail189
import SixSingletonFivePairTail189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private vt vp from SixSingletonFivePairTail189
open private erased_pair_retains_six_ore from SixSingletonFiveThreeNonadjacentTinyCore189
open private d8 p5 from SixSingletonFiveShallowRoute189
open private erase_internal_deg from SixSingletonDarkOre189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem three_join_marked_split {L R S : Finset V} {T : V} (F : ProfileThree G L R S T)
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

private theorem spare_free_root {L R S : Finset V} {T z w h n : V} (F : ProfileThree G L R S T)
    (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zw : z≠w) (zh : z≠h) (wh : w≠h)
    (zl : (inside G D z).card≤2) (wl : (inside G D w).card≤2)
    (hh : 4≤(inside G D h).card) (nm : n∈(D.erase z).erase w) :
    ∃ l∈L∪R,RouteOn G ((D.erase z).erase w) l n := by
  classical
  let E := (D.erase z).erase w
  have sE : S⊆E := fun u um=>mem_erase.mpr ⟨fun e=>(mem_sdiff.mp wm).2 (e ▸ um),
    mem_erase.mpr ⟨fun e=>(mem_sdiff.mp zm).2 (e ▸ um),F.core_sub um⟩⟩
  have hE : h∈E := mem_erase.mpr ⟨wh.symm,mem_erase.mpr ⟨zh.symm,(mem_sdiff.mp hm).1⟩⟩
  have tE : T∈E := sE F.deepS
  have wE : w∈D.erase z := mem_erase.mpr ⟨zw.symm,(mem_sdiff.mp wm).1⟩
  have e6 : E.card=6 := by
    change ((D.erase z).erase w).card=6
    rw [card_erase_of_mem wE,card_erase_of_mem (mem_sdiff.mp zm).1,d8]
  have lost (u : V) : (inside G D u).card≤(inside G E u).card+2 := by
    have a := erase_internal_deg (G:=G) D z u
    have b := erase_internal_deg (G:=G) (D.erase z) w u
    change _≤(inside G E u).card+1 at b
    omega
  have ht : 3≤(inside G E T).card := by have l := lost T; have d := F.deep6; omega
  have h2 : 2≤(inside G E h).card := by have l := lost h; omega
  have W : D\S={z,w,h} := by
    have sub : ({z,w,h}:Finset V)⊆D\S := insert_subset zm (insert_subset wm (singleton_subset_iff.mpr hm))
    apply (eq_of_subset_of_card_le sub ?_).symm
    rw [F.balance,card_insert_of_not_mem (by simp [zw,zh]),card_insert_of_not_mem (by simp [wh]),card_singleton]
  have core : S=insert T (L∪R) := by
    have sub : insert T (L∪R)⊆S := insert_subset F.deepS (union_subset F.left_sub F.right_sub)
    have no : T∉L∪R := fun h=>(mem_union.mp h).elim F.deepL F.deepR
    apply (eq_of_subset_of_card_le sub ?_).symm
    rw [card_insert_of_not_mem no,card_union_of_disjoint F.apart,F.l2,F.r2]
    have k := card_sdiff F.core_sub
    rw [F.balance,d8] at k
    have l := card_le_card F.core_sub
    rw [d8] at l
    omega
  have strict {q : V} (qm : q∈E) (qt : q≠T) (qh : q≠h) : q∈L∪R := by
    by_cases qs : q∈S
    · rw [core,mem_insert] at qs
      exact qs.resolve_left qt
    have j : q∈D\S := mem_sdiff.mpr ⟨(mem_erase.mp (mem_erase.mp qm).2).2,qs⟩
    rw [W,mem_insert,mem_insert,mem_singleton] at j
    exact (qh ((j.resolve_left (mem_erase.mp (mem_erase.mp qm).2).1).resolve_left (mem_erase.mp qm).1)).elim
  have finishT (p : RouteOn G E T n) : ∃ l∈L∪R,RouteOn G E l n := by
    obtain ⟨l,lm,lT,lh,q⟩ := route_avoid_two_free E p.reverse hE ht
    exact ⟨l,strict lm lT lh,q.reverse⟩
  obtain ⟨l,lm,route⟩ := rooted_side_route (G:=G) E nm (fun u um v vm uv _=>by
    rw [e6]; exact erased_pair_retains_six_ore F zm wm hm zw zh wh zl wl hh u um v vm uv)
  by_cases lT : l=T
  · subst l
    exact finishT route
  by_cases lh : l=h
  · subst l
    obtain ⟨v,vm,vh,path⟩ := route_avoid_free_end E route.reverse h2
    by_cases vT : v=T
    · subst v
      exact finishT path.reverse
    exact ⟨v,strict vm vT vh,path.reverse⟩
  exact ⟨l,strict lm lT lh,route⟩

/-- The nonadjacent degree-one/two pair also routes when the third
balance is high. Root through their six-vertex complement, then use
the common triple and second tiny balance in the port tail. -/
theorem three_balances_nonadjacent_two_tiny {L R S : Finset V} {T z w h : V}
    (F : ProfileThree G L R S T) (hc : G.Connected)
    (even : ∀ i,(EvenFrom G i).card≤7)
    (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zw : z≠w) (zh : z≠h) (wh : w≠h) (notAdj : ¬G.Adj z w)
    (zl : (inside G D z).card≤2) (wl : (inside G D w).card≤2)
    (hh : 4≤(inside G D h).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let E := (D.erase z).erase w
  have zd := (mem_sdiff.mp zm).1
  have wd := (mem_sdiff.mp wm).1
  have hit : ∃ q∈E,G.Adj q z := by
    by_contra no
    have sub : G.neighborFinset z⊆P := by
      intro u um
      have e := (mem_neighborFinset _ _ _).mp um
      exact (mem_union.mp (F.darkBounds z zd u e)).resolve_left (fun d=>
        no ⟨u,mem_erase.mpr ⟨fun h=>notAdj (h ▸ e),mem_erase.mpr ⟨e.ne.symm,d⟩⟩,e.symm⟩)
    have k := card_le_card sub
    rw [card_neighborFinset_eq_degree,p5] at k
    have h := F.darkHigh z zd
    omega
  obtain ⟨q,qm,qz⟩ := hit
  obtain ⟨l,lm,path⟩ := spare_free_root F zm wm hm zw zh wh zl wl hh qm
  have p := path.suffix qz (fun m=>(mem_erase.mp (mem_erase.mp m).2).1 rfl)
  obtain ⟨c,cm,t,tm,zc,tail⟩ := tiny_common_route F hc even zd wd zl wl
  have uD : insert z E⊆D := insert_subset zd (fun u um=>(mem_erase.mp (mem_erase.mp um).2).2)
  have jD : ({w}:Finset V)⊆D := singleton_subset_iff.mpr wd
  have sep : Disjoint (insert z E) ({w}:Finset V) := by
    apply disjoint_left.mpr
    intro i im iw
    rw [mem_singleton] at iw
    subst i
    exact (mem_insert.mp im).elim zw.symm (fun m=>(mem_erase.mp m).1 rfl)
  have eq : insert w (insert z E)=D := by
    change insert w (insert z ((D.erase z).erase w))=D
    rw [insert_comm,insert_erase (mem_erase.mpr ⟨zw.symm,wd⟩),insert_erase zd]
  have cv : insert z E∪({w}:Finset V)=D := by
    rw [←eq]
    ext v
    simp only [mem_union,mem_insert,mem_singleton]
    tauto
  have q' : RouteOn G (({w}:Finset V)∪K) c t := by
    have unionK : ({w}:Finset V)∪K=insert w K := by
      ext v
      simp only [mem_union,mem_singleton,mem_insert]
    rwa [unionK]
  rcases mem_union.mp lm with lL|lR
  · exact three_join_marked_split F true uD jD sep cv (F.xL l lL) p zc q' (.inl tm)
  exact three_join_marked_split F false uD jD sep cv (F.yR l lR) p zc q' (.inl tm)

#print axioms three_balances_nonadjacent_two_tiny
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
