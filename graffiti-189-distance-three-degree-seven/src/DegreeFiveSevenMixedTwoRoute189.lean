import DegreeFiveOreFiveExceptPair189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem four_a_bridge_two_inner_free (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (b3 : (S.L.filter (G.Adj b)).card=3)
    (i2 : (farNonports S.L a b G).card=2)
    (w1 : (visibleBPorts S.L a b G).card=1) (foreign : S.foreignA.card=3)
    (showI : farNonports S.L a b G⊆secondA G S.L a) (bridge : portBridge S) :
    ∃ u v,G.Adj a u ∧ RouteOn G S.L u v := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  let W := visibleBPorts S.L a b G
  let D := B\W
  change A.card=4 at a4
  change B.card=3 at b3
  change I.card=2 at i2
  change W.card=1 at w1
  have aL : A⊆S.L := filter_subset _ _
  have bL : B⊆S.L := filter_subset _ _
  have iL : I⊆S.L := filter_subset _ _
  have wb : W⊆B := fun _ h=>mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩
  have dB : D⊆B := sdiff_subset
  have aB : Disjoint A B := disjoint_left.mpr
    (fun x xa xb=>not_common far (mem_filter.mp xa).2 (mem_filter.mp xb).2)
  have aI : Disjoint A I := disjoint_left.mpr (fun x xa xi=>(mem_filter.mp xi).2.1 (mem_filter.mp xa).2)
  have iB : Disjoint I B := disjoint_left.mpr (fun x xi xb=>(mem_filter.mp xi).2.2 (mem_filter.mp xb).2)
  have perm : ∀ x∈S.L,x∈A ∨ x∈B ∨ x∈I := by
    intro x hx
    have shape := left_port_partition S far
    rw [←shape] at hx
    exact (mem_union.mp hx).elim (fun h=>(mem_union.mp h).imp id Or.inl) (fun h=>.inr (.inr h))
  obtain ⟨p,pl,v,vl,ap,pv,bv⟩ := bridge
  have pa : p∈A := mem_filter.mpr ⟨pl,ap⟩
  have vv : v∈W := mem_filter.mpr ⟨vl,bv,p,pl,ap,pv⟩
  have vb := wb vv
  have wEq : W={v} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr vv)
    (by rw [card_singleton,w1])).symm
  have d2' : D.card=2 := by change (B\W).card=2; rw [card_sdiff wb,b3,w1]
  obtain ⟨x,xd,y,yd,xy⟩ := one_lt_card.mp (show 1<D.card by omega)
  have sel : ∃ h∈D,∃ l∈D,h≠l ∧ 5≤G.degree h := by
    rcases degree x y xy with gx|gy
    · exact ⟨x,xd,y,yd,xy,gx⟩
    exact ⟨y,yd,x,xd,xy.symm,gy⟩
  obtain ⟨h,hd,l,ld,hl,h5⟩ := sel
  have hb := dB hd
  have lb := dB ld
  have hv : h≠v := fun e=>(mem_sdiff.mp hd).2 (e.symm ▸ vv)
  have lv : l≠v := fun e=>(mem_sdiff.mp ld).2 (e.symm ▸ vv)
  have hFull (z : V) (zd : z∈D) (z5 : 5≤G.degree z) :
      (∀ r∈B,z≠r → G.Adj z r) ∧ ∀ i∈I,G.Adj z i := by
    have can := far_dark_b_port_candidates S far (dB zd) (mem_sdiff.mp zd).2
    change G.neighborFinset z⊆insert b ((B.erase z)∪I) at can
    exact far_port_full_at_tight_pool (dB zd) can (by omega) z5
  have vh := ((hFull h hd h5).1 v vb hv).symm
  have hL := (hFull h hd h5).1 l lb hl
  have no (q : V) (qr : q∈D) (x : V) (xa : x∈A) : ¬G.Adj x q := by
    obtain ⟨xl,ax⟩ := mem_filter.mp xa
    obtain ⟨ql,bq⟩ := mem_filter.mp (dB qr)
    exact fun xq=>(mem_sdiff.mp qr).2 (mem_filter.mpr ⟨ql,bq,x,xl,ax,xq⟩)
  have full (q : V) (qa : q∈A) (qv : G.Adj q v) :
      (∀ r∈A,q≠r → G.Adj q r) ∧ ∀ i∈I,G.Adj q i := by
    obtain ⟨ql,aq⟩ := mem_filter.mp qa
    have b2 := d2 hc (show q ≠ b from fun e => S.leftOff.2 (e ▸ ql))
      (fun e=>not_common far aq e.symm) qv bv.symm
    have h2 := d2 hc (fun e=>disjoint_left.mp aB (e ▸ qa) hb) (no h hd q qa) qv vh
    exact bridge_two_locals_full S hc far even foreign showI qa hb b2 h2
  have pFull := full p pa pv
  have lNoI (i : V) (ii : i∈I) : ¬G.Adj l i := by
    intro li
    have b2 := d2 hc (show p ≠ b from fun e => S.leftOff.2 (e ▸ pl)) (fun e=>not_common far ap e.symm) pv bv.symm
    have h2 := d2 hc (fun e=>disjoint_left.mp aB (e ▸ pa) hb) (no h hd p pa) pv vh
    have l2 := d2 hc (fun e=>disjoint_left.mp aB (e ▸ pa) lb) (no l ld p pa) (pFull.2 i ii) li.symm
    let P : Finset V := {b,h,l}
    have loc : P⊆insert b S.L := insert_subset_iff.mpr ⟨mem_insert_self _ _,
      insert_subset_iff.mpr ⟨mem_insert_of_mem (bL hb),singleton_subset_iff.mpr (mem_insert_of_mem (bL lb))⟩⟩
    have ds : P⊆DistanceTwo G p := insert_subset_iff.mpr ⟨b2,
      insert_subset_iff.mpr ⟨h2,singleton_subset_iff.mpr l2⟩⟩
    have g := local_distance_two_at_foreign_three S hc even foreign pl ap loc ds
    have bh : b≠h := fun e=>S.leftOff.2 (e.symm ▸ bL hb)
    have bl : b≠l := fun e=>S.leftOff.2 (e.symm ▸ bL lb)
    have cp : P.card=3 := by simp [P,bh,bl,hl]
    omega
  have low : ¬5≤G.degree l := by
    intro t
    obtain ⟨i,ii⟩ := card_pos.mp (show 0<I.card by omega)
    exact lNoI i ii ((hFull l ld t).2 i ii)
  have hi (q : V) (qL : q∈A∪I) : 5≤G.degree q := by
    have ne : q≠l := by
      intro e
      exact (mem_union.mp qL).elim (fun qa=>disjoint_left.mp aB (e ▸ qa) lb)
        (fun qi=>disjoint_left.mp iB (e ▸ qi) lb)
    exact (degree q l ne).resolve_right low
  have bEq : B={v,h,l} := by
    have sub : ({v,h,l} : Finset V)⊆B := insert_subset_iff.mpr
      ⟨vb,insert_subset_iff.mpr ⟨hb,singleton_subset_iff.mpr lb⟩⟩
    have cap : ({v,h,l} : Finset V).card=3 := by simp [hv.symm,lv.symm,hl]
    exact (eq_of_subset_of_card_le sub (by omega)).symm
  let K := A.erase p
  let U := K∪I
  have ka : K⊆A := erase_subset _ _
  have k3 : K.card=3 := by change (A.erase p).card=3; rw [card_erase_of_mem pa,a4]
  have dis : Disjoint K I := aI.mono ka (Subset.refl _)
  have sz : U.card=5 := by change (K∪I).card=5; rw [card_union_of_disjoint dis,k3,i2]
  have pOff : p∉U := fun h=>(mem_union.mp h).elim
    (fun pk=>(mem_erase.mp pk).1 rfl) (fun pi=>disjoint_left.mp aI pa pi)
  have dA (q : V) (qk : q∈K) : 3≤(inside G U q).card := by
    have qa := ka qk
    have qu : q∈U := mem_union_left _ qk
    have high := hi q (mem_union_left _ qa)
    obtain ⟨ql,aq⟩ := mem_filter.mp qa
    by_cases qv : G.Adj q v
    · have f := full q qa qv
      have sub : U.erase q⊆inside G U q := by
        intro r rr
        obtain ⟨rq,ru⟩ := mem_erase.mp rr
        refine mem_filter.mpr ⟨ru,?_⟩
        exact (mem_union.mp ru).elim (fun rk=>f.1 r (ka rk) rq.symm) (fun ri=>f.2 r ri)
      have m := card_le_card sub
      rw [card_erase_of_mem qu,sz] at m
      omega
    have sub : G.neighborFinset q⊆insert a (insert p (inside G U q)) := by
      intro r rm
      have qr := (mem_neighborFinset G q r).mp rm
      rcases left_boundary S q ql r qr with e|e|rl
      · exact mem_insert.mpr (.inl e)
      · exact (not_common far aq (e ▸ qr.symm)).elim
      rcases perm r rl with ra|rb|ri
      · by_cases rp : r=p
        · exact mem_insert_of_mem (mem_insert.mpr (.inl rp))
        exact mem_insert_of_mem (mem_insert_of_mem
          (mem_filter.mpr ⟨mem_union_left _ (mem_erase.mpr ⟨rp,ra⟩),qr⟩))
      · have eq : r=v ∨ r=h ∨ r=l := by simpa [bEq] using rb
        rcases eq with t|t|t
        · exact (qv (t ▸ qr)).elim
        · exact (no h hd q qa (t ▸ qr)).elim
        exact (no l ld q qa (t ▸ qr)).elim
      exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨mem_union_right _ ri,qr⟩))
    have n := (card_le_card sub).trans (card_insert_le a _)
    have m := card_insert_le p (inside G U q)
    rw [card_neighborFinset_eq_degree] at n
    omega
  have dI (q : V) (qi : q∈I) : 2≤(inside G U q).card := by
    have high := hi q (mem_union_right _ qi)
    obtain ⟨ql,aq,bq⟩ := mem_filter.mp qi
    have sub : G.neighborFinset q⊆insert p (insert v (insert h (inside G U q))) := by
      intro r rm
      have qr := (mem_neighborFinset G q r).mp rm
      rcases left_boundary S q ql r qr with e|e|rl
      · exact (aq (e ▸ qr.symm)).elim
      · exact (bq (e ▸ qr.symm)).elim
      rcases perm r rl with ra|rb|ri
      · by_cases rp : r=p
        · exact mem_insert.mpr (.inl rp)
        exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
          (mem_filter.mpr ⟨mem_union_left _ (mem_erase.mpr ⟨rp,ra⟩),qr⟩)))
      · have eq : r=v ∨ r=h ∨ r=l := by simpa [bEq] using rb
        rcases eq with t|t|t
        · exact mem_insert_of_mem (mem_insert.mpr (.inl t))
        · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert.mpr (.inl t)))
        exact (lNoI q qi (t ▸ qr).symm).elim
      exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
        (mem_filter.mpr ⟨mem_union_right _ ri,qr⟩)))
    have n := (card_le_card sub).trans (card_insert_le p _)
    have m := card_insert_le v (insert h (inside G U q))
    have c := card_insert_le h (inside G U q)
    rw [card_neighborFinset_eq_degree] at n
    omega
  obtain ⟨u,uk,q,path⟩ := rooted_route_a3_i2_from_induced_degrees k3 i2 dis dA dI
  have qu : q∈U := by
    obtain ⟨w,_,ws⟩ := path
    exact (ws q).mp w.end_mem_support
  have qp : G.Adj q p := by
    apply Adj.symm
    rcases mem_union.mp qu with qk|qi
    · exact pFull.1 q (ka qk) (mem_erase.mp qk).1.symm
    exact pFull.2 q qi
  have pre := path.suffix qp pOff
  have tail : RouteOn G B v l := by
    rw [bEq]
    exact RouteOn.three vh hL lv.symm
  have e : insert p U=A∪I := by
    ext x
    by_cases e : x=p
    · subst x
      simp [pa]
    simp [U,K,e]
  have d : Disjoint (A∪I) B := disjoint_union_left.mpr ⟨aB,iB⟩
  have cov : (A∪I)∪B=S.L := by rw [union_right_comm]; exact left_port_partition S far
  have r : RouteOn G (A∪I) u p := e ▸ pre
  exact ⟨u,l,(mem_filter.mp (ka uk)).2,cov ▸ r.join tail d pv⟩

#print axioms four_a_bridge_two_inner_free
end Graffiti189LongestPath.CrossSaturation.Split.Five
