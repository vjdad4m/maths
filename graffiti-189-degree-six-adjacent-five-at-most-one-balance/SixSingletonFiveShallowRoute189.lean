import SixSingletonAdjacentProfiles189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private two_local_counts from SixCutFar189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
abbrev V := Fin 16
abbrev a : V := 0
abbrev b : V := 1
abbrev s : V := 2
abbrev x : V := 3
abbrev y : V := 4
def K : Finset V := {5,6,7}
def D : Finset V := {8,9,10,11,12,13,14,15}
def P : Finset V := insert x (insert y K)
private theorem k3 : K.card=3 := by decide
private theorem d8 : D.card=8 := by decide
private theorem p5 : P.card=5 := by decide
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure Profile (G : SimpleGraph V) [DecidableRel G.Adj] (L R S : Finset V) : Prop where
  left_sub : L⊆S
  right_sub : R⊆S
  core_sub : S⊆D
  strict6 : 6≤(L∪R).card
  apart : Disjoint L R
  l2 : 2≤L.card
  r2 : 2≤R.card
  balance : (D\S).card≤1
  sa : G.Adj s a
  sb : G.Adj s b
  ax : G.Adj a x
  by' : G.Adj b y
  commonA : ∀ c∈K,G.Adj a c
  commonB : ∀ c∈K,G.Adj b c
  xL : ∀ z∈L,G.Adj x z
  yR : ∀ z∈R,G.Adj y z
  dark5 : ∀ z∈S,5≤(inside G D z).card
  darkHigh : ∀ z∈D,6≤G.degree z
  commonHigh : ∀ c∈K,6≤G.degree c
  commonBounds : ∀ c∈K,∀ z,G.Adj c z → z∈insert a (insert b (P∪(D\S)))
  darkBounds : ∀ d∈D,∀ z,G.Adj d z → z∈D∪P

private theorem finish_plain {l r c t : V}
    (p : RouteOn G D l r) (q : RouteOn G K c t) (sa : G.Adj s a) (ax : G.Adj a x)
    (xl : G.Adj x l) (ry : G.Adj r y) (yc : G.Adj y c) (tb : G.Adj t b) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  have p1 := p.prefix xl (by decide)
  have p2 := p1.prefix ax (by decide)
  have p3 := p2.prefix sa (by decide)
  have q1 := q.prefix yc (by decide)
  have q2 := q1.suffix tb (by decide)
  obtain ⟨w,wp,ws⟩ := p3.join q2 (by decide) ry
  exact ⟨s,b,w,wp,fun z=>(ws z).mpr ((by decide : ∀ u : V,
    u∈insert s (insert a (insert x D)) ∪ insert b (insert y K)) z)⟩

private theorem finish_by_balance {l w c t : V}
    (p : RouteOn G D l w) (q : RouteOn G K c t) (sa : G.Adj s a) (ax : G.Adj a x)
    (xl : G.Adj x l) (wc : G.Adj w c) (tb : G.Adj t b) (by' : G.Adj b y) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  have p1 := p.prefix xl (by decide)
  have p2 := p1.prefix ax (by decide)
  have p3 := p2.prefix sa (by decide)
  have q1 := q.suffix tb (by decide)
  have q2 := q1.suffix by' (by decide)
  obtain ⟨w,wp,ws⟩ := p3.join q2 (by decide) wc
  exact ⟨s,y,w,wp,fun z=>(ws z).mpr ((by decide : ∀ u : V,
    u∈insert s (insert a (insert x D)) ∪ insert y (insert b K)) z)⟩

/-- Five visible vertices and at most one balanced depth-two dark vertex:
the normalized board also allows a single deeper dark core vertex. -/
theorem traceable_of_shallow_five_at_most_one_balance {L R S : Finset V}
    (F : Profile G L R S) (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let W := D\S
  have sub : S⊆D := F.core_sub
  have LL : L.Nonempty := card_pos.mp (by have h := F.l2; omega)
  have RR : R.Nonempty := card_pos.mp (by have h := F.r2; omega)
  obtain ⟨l,ll⟩ := LL
  obtain ⟨r,rr⟩ := RR
  have lr : l≠r := fun e=>disjoint_left.mp F.apart ll (e.symm ▸ rr)
  by_cases wb : W.Nonempty
  · have W1 : W.card=1 := by have h := card_pos.mpr wb; have u := F.balance; change W.card≤1 at u; omega
    obtain ⟨z,zW⟩ := card_eq_one.mp W1
    have zw : z∈W := by rw [zW]; simp
    have ⟨zd,zs⟩ := mem_sdiff.mp zw
    have s7 : S.card=7 := by
      have h : W.card=D.card-S.card := card_sdiff sub
      rw [W1,d8] at h
      have k := card_le_card sub
      rw [d8] at k
      omega
    have eq : D.erase z=S := by
      have sE : S⊆D.erase z := fun t tm=>mem_erase.mpr ⟨fun e=>zs (e ▸ tm),sub tm⟩
      exact (eq_of_subset_of_card_le sE (by rw [card_erase_of_mem zd,d8,s7])).symm
    have ext (c : V) (ck : c∈K) : ¬(G.Adj c x ∧ G.Adj c y) := by
      rintro ⟨cx,cy⟩
      have ss : L∪R⊆DistanceTwo G c := by
        intro t tm
        have tmS := (mem_union.mp tm).elim (fun m=>F.left_sub m) (fun m=>F.right_sub m)
        have td := sub tmS
        have ct : c≠t := fun h=>disjoint_left.mp (by decide : Disjoint K D) ck (h.symm ▸ td)
        have tn : ¬G.Adj c t := by
          intro h
          rcases mem_insert.mp (F.commonBounds c ck t h) with e|e
          · exact (by decide : a∉D) (e ▸ td)
          rcases mem_insert.mp e with e|e
          · exact (by decide : b∉D) (e ▸ td)
          rcases mem_union.mp e with p|p
          · exact disjoint_left.mp (by decide : Disjoint P D) p td
          exact (mem_sdiff.mp p).2 tmS
        rcases mem_union.mp tm with h|h
        · exact d2 hc ct tn cx (F.xL t h)
        exact d2 hc ct tn cy (F.yR t h)
      have sn : ¬G.Adj c s := by
        intro h
        have g := F.commonBounds c ck s h
        have j : s∈insert a (insert b (P∪D)) := by
          rcases mem_insert.mp g with p|p
          · exact mem_insert.mpr (.inl p)
          rcases mem_insert.mp p with p|p
          · exact mem_insert_of_mem (mem_insert.mpr (.inl p))
          apply mem_insert_of_mem
          apply mem_insert_of_mem
          exact (mem_union.mp p).elim (fun h=>mem_union_left _ h)
            (fun h=>mem_union_right _ (mem_sdiff.mp h).1)
        exact (by decide : s∉insert a (insert b (P∪D))) j
      have sc : c≠s := fun e=>(by decide : s∉K) (e ▸ ck)
      have st := d2 hc sc sn (F.commonA c ck).symm F.sa.symm
      have sd : s∉L∪R := fun h=>(by decide : s∉D)
        (sub ((mem_union.mp h).elim (fun m=>F.left_sub m) (fun m=>F.right_sub m)))
      have k := card_le_card (insert_subset st ss)
      rw [card_insert_of_not_mem sd] at k
      have hi := distanceTwo_le_of_even 6 c (even c)
      have h := F.strict6
      omega
    have cliqueHit (c : V) (ck : c∈K) :
        G.Adj c z ∧ ∀ t∈K,t≠c → G.Adj c t := by
      let u := if G.Adj c x then x else y
      have cb : G.neighborFinset c⊆insert a (insert b (insert u (insert z (K.erase c)))) := by
        intro t tm
        have ct := (mem_neighborFinset _ _ _).mp tm
        rcases mem_insert.mp (F.commonBounds c ck t ct) with h|h
        · exact mem_insert.mpr (.inl h)
        apply mem_insert_of_mem
        rcases mem_insert.mp h with h|h
        · exact mem_insert.mpr (.inl h)
        apply mem_insert_of_mem
        rcases mem_union.mp h with p|p
        · rcases mem_insert.mp p with p|p
          · exact mem_insert.mpr (.inl (p.trans (if_pos (p ▸ ct)).symm))
          rcases mem_insert.mp p with p|p
          · have nx : ¬G.Adj c x := fun cx=>ext c ck ⟨cx,p ▸ ct⟩
            exact mem_insert.mpr (.inl (p.trans (if_neg nx).symm))
          exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨ct.ne.symm,p⟩))
        have pz : t=z := by simpa only [zW,mem_singleton] using (show t∈W from p)
        exact mem_insert_of_mem (mem_insert.mpr (.inl pz))
      have size : (insert a (insert b (insert u (insert z (K.erase c))))).card≤6 := by
        have i := card_insert_le a (insert b (insert u (insert z (K.erase c))))
        have j := card_insert_le b (insert u (insert z (K.erase c)))
        have k := card_insert_le u (insert z (K.erase c))
        have m := card_insert_le z (K.erase c)
        have n := card_erase_add_one ck
        have q : K.card=3 := k3
        omega
      have total := eq_of_subset_of_card_le cb (by rw [card_neighborFinset_eq_degree]; exact size.trans (F.commonHigh c ck))
      constructor
      · exact (mem_neighborFinset _ _ _).mp (total.symm ▸
          mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))))
      intro t tk tc
      exact (mem_neighborFinset _ _ _).mp (total.symm ▸
        mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨tc,tk⟩)))))
    have clique : CompleteOn G K := fun c cm t tk ct=>(cliqueHit c cm).2 t tk ct.symm
    have hit : ∃ t∈S,G.Adj z t := by
      by_contra no
      have size : G.neighborFinset z⊆P := by
        intro t tm
        have zt := (mem_neighborFinset _ _ _).mp tm
        rcases mem_union.mp (F.darkBounds z zd t zt) with tD|tP
        · by_cases ts : t∈S
          · exact (no ⟨t,ts,zt⟩).elim
          have tw : t∈W := mem_sdiff.mpr ⟨tD,ts⟩
          have tz : t=z := by simpa only [zW,mem_singleton] using tw
          exact (zt.ne tz.symm).elim
        exact tP
      have h := card_le_card size
      rw [card_neighborFinset_eq_degree,p5] at h
      have high := F.darkHigh z zd
      omega
    obtain ⟨t,ts,zt⟩ := hit
    obtain ⟨u,ul,ut⟩ := exists_ne_of_one_lt_card (s:=L) (by have h := F.l2; omega) t
    have p : RouteOn G S u t := terminal_route_on_of_local_ore S (F.left_sub ul) ts ut
      (fun i im j jm _ _=>by
        have di := F.dark5 i im
        have dj := F.dark5 j jm
        have ri := erase_internal_deg (G:=G) D z i
        have rj := erase_internal_deg (G:=G) D z j
        rw [eq] at ri rj
        omega)
    have p' := p.suffix zt.symm zs
    have eq' : insert z S=D := by rw [←eq,insert_erase zd]
    rw [eq'] at p'
    have cK : (5:V)∈K := by decide
    obtain ⟨q,e,ep,es⟩ := rooted_path_in_clique K clique cK
    exact finish_by_balance p' ⟨e,ep,es⟩ F.sa F.ax (F.xL u ul)
      (cliqueHit 5 cK).1.symm (F.commonB q ((es q).mp e.end_mem_support)).symm F.by'
  have z0 : W=∅ := not_nonempty_iff_eq_empty.mp wb
  have eqD : S=D := by
    have f : S∪W=D := union_sdiff_of_subset sub
    simpa [z0] using f
  have dRoute : RouteOn G D l r :=
    terminal_route_on_of_local_ore D (sub (F.left_sub ll)) (sub (F.right_sub rr)) lr
      (fun u um v vm _ _=>by
        have ul : u∈S := eqD.symm ▸ um
        have vl : v∈S := eqD.symm ▸ vm
        have h := F.dark5 u ul
        have j := F.dark5 v vl
        have d : D.card=8 := d8
        omega)
  have normal (c : V) (ck : c∈K) : G.neighborFinset c=insert a (insert b (P.erase c)) := by
    have sub : G.neighborFinset c⊆insert a (insert b (P.erase c)) := by
      intro t tm
      have ct := (mem_neighborFinset _ _ _).mp tm
      rcases mem_insert.mp (F.commonBounds c ck t ct) with h|h
      · exact mem_insert.mpr (.inl h)
      rcases mem_insert.mp h with h|h
      · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
      rcases mem_union.mp h with p|p
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨ct.ne.symm,p⟩))
      have p' : t∈W := p
      simp [z0] at p'
    have cP : c∈P := mem_insert_of_mem (mem_insert_of_mem ck)
    apply eq_of_subset_of_card_le sub
    rw [card_neighborFinset_eq_degree]
    have u := card_insert_le a (insert b (P.erase c))
    have v := card_insert_le b (P.erase c)
    have w := card_erase_add_one cP
    have hi := F.commonHigh c ck
    have pp : P.card=5 := p5
    omega
  have clique : CompleteOn G K := by
    intro c ck t tk ct
    have p : t∈P := mem_insert_of_mem (mem_insert_of_mem tk)
    exact (mem_neighborFinset _ _ _).mp ((normal c ck).symm ▸
      mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨ct.symm,p⟩)))
  have cK : (5:V)∈K := by decide
  have yC : G.Adj y 5 := by
    have h : y∈insert a (insert b (P.erase (5:V))) := by decide
    exact ((mem_neighborFinset _ _ _).mp ((normal 5 cK).symm ▸ h)).symm
  obtain ⟨q,e,ep,es⟩ := rooted_path_in_clique K clique cK
  exact finish_plain dRoute ⟨e,ep,es⟩ F.sa F.ax (F.xL l ll) (F.yR r rr).symm yC
    (F.commonB q ((es q).mp e.end_mem_support)).symm

#print axioms traceable_of_shallow_five_at_most_one_balance
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
