import DegreeFiveSevenMixedDrop24189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem four_a_bridge_one_inner_geometry (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (b4 : (S.L.filter (G.Adj b)).card=4)
    (i1 : (farNonports S.L a b G).card=1)
    (w2 : (visibleBPorts S.L a b G).card≤2) (foreign : S.foreignA.card=3)
    (showI : farNonports S.L a b G⊆secondA G S.L a) (bridge : portBridge S) :
    let A := S.localA
    let B := S.L.filter (G.Adj b)
    let I := farNonports S.L a b G
    CompleteOn G (A∪I) ∧ ∃ v w h l : V,
      v≠w ∧ v≠h ∧ v≠l ∧ w≠h ∧ w≠l ∧ h≠l ∧
      B={v,w,h,l} ∧ G.Adj v h ∧ G.Adj w h ∧ G.Adj h l ∧
      ((G.Adj v w ∧ ∃ x∈A,G.Adj x v) ∨
        ∃ x∈A,∃ y∈A,x≠y ∧ G.Adj v x ∧ G.Adj y w) := by
  classical
  dsimp only
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  let W := visibleBPorts S.L a b G
  let T := B\W
  let H := T.filter (fun x=>5≤G.degree x)
  change A.card=4 at a4
  change B.card=4 at b4
  change I.card=1 at i1
  change W.card≤2 at w2
  have wb : W⊆B := fun _ hw=>mem_filter.mpr ⟨(mem_filter.mp hw).1,(mem_filter.mp hw).2.1⟩
  have tb : T⊆B := sdiff_subset
  have ht : H⊆T := filter_subset _ _
  have bL : B⊆S.L := filter_subset _ _
  have iL : I⊆S.L := filter_subset _ _
  have sep : Disjoint A B := disjoint_left.mpr
    (fun x xa xb=>not_common far (mem_filter.mp xa).2 (mem_filter.mp xb).2)
  obtain ⟨p,pl,v,vl,ap,pv,bv⟩ := bridge
  have pa : p∈A := mem_filter.mpr ⟨pl,ap⟩
  have vv : v∈W := mem_filter.mpr ⟨vl,bv,p,pl,ap,pv⟩
  have vb := wb vv
  have pnb : p≠b := fun e=>S.leftOff.2 (e ▸ pl)
  have b2 := d2 hc pnb (fun e=>not_common far ap e.symm) pv bv.symm
  have td : T.card+W.card=B.card := card_sdiff_add_card_eq_card wb
  have c := count_high_subset_of_one_low degree T
  change T.card≤H.card+1 at c
  have hFull (h : V) (hh : h∈H) :
      (∀ r∈B,h≠r → G.Adj h r) ∧ (∀ r∈I,G.Adj h r) := by
    obtain ⟨ht,h5⟩ := mem_filter.mp hh
    have cand := far_dark_b_port_candidates S far (mem_sdiff.mp ht).1 (mem_sdiff.mp ht).2
    change G.neighborFinset h⊆insert b ((B.erase h)∪I) at cand
    exact far_port_full_at_tight_pool (tb ht) cand (by omega) h5
  have darkNo (q : V) (qt : q∈T) (p : V) (pa : p∈A) : ¬G.Adj p q := by
    obtain ⟨qb,nt⟩ := mem_sdiff.mp qt
    obtain ⟨ql,bq⟩ := mem_filter.mp qb
    obtain ⟨pl,ap⟩ := mem_filter.mp pa
    exact fun h=>nt (mem_filter.mpr ⟨ql,bq,p,pl,ap,h⟩)
  have charge (q : V) (qa : q∈A) {X : Finset V}
      (loc : X⊆insert b S.L) (chg : X⊆DistanceTwo G q) : X.card≤2 :=
    local_distance_two_at_foreign_three S hc even foreign (mem_filter.mp qa).1
      (mem_filter.mp qa).2 loc chg
  have bOff : b∉H := fun e=>S.leftOff.2 (bL (tb (ht e)))
  have hh2 : H.card≤1 := by
    have m : H⊆DistanceTwo G p := by
      intro j jh
      have jt := ht jh
      have jv : j≠v := fun e=>(mem_sdiff.mp jt).2 (e.symm ▸ vv)
      exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) (tb jt))
        (darkNo j jt p pa) pv ((hFull j jh).1 v vb jv).symm
    have n := charge p pa (insert_subset_iff.mpr ⟨mem_insert_self _ _,fun j jh=>
      mem_insert_of_mem (bL (tb (ht jh)))⟩) (insert_subset_iff.mpr ⟨b2,m⟩)
    rw [card_insert_of_not_mem bOff] at n
    omega
  have T2 : T.card=2 := by omega
  have ww2 : W.card=2 := by omega
  have h1 : H.card=1 := by omega
  obtain ⟨h,hh⟩ := card_pos.mp (show 0<H.card by omega)
  have hT := ht hh
  obtain ⟨l,ll⟩ := card_pos.mp (show 0<(T.erase h).card by rw [card_erase_of_mem hT,T2]; decide)
  obtain ⟨lh,lT⟩ := mem_erase.mp ll
  have low : ¬5≤G.degree l := by
    intro high
    have m : l∈H := mem_filter.mpr ⟨lT,high⟩
    have n := one_lt_card.mpr ⟨l,m,h,hh,lh⟩
    omega
  obtain ⟨w,wOff⟩ := card_pos.mp (show 0<(W.erase v).card by rw [card_erase_of_mem vv,ww2]; decide)
  obtain ⟨wv,wW⟩ := mem_erase.mp wOff
  have wB := wb wW
  have lB := tb lT
  have hB := tb hT
  have vh : v≠h := fun e=>(mem_sdiff.mp hT).2 (e ▸ vv)
  have vl' : v≠l := fun e=>(mem_sdiff.mp lT).2 (e ▸ vv)
  have wh : w≠h := fun e=>(mem_sdiff.mp hT).2 (e ▸ wW)
  have wl : w≠l := fun e=>(mem_sdiff.mp lT).2 (e ▸ wW)
  have vw := wv.symm
  have BQ : B={v,w,h,l} := by
    have sub : ({v,w,h,l} : Finset V)⊆B := insert_subset_iff.mpr ⟨vb,
      insert_subset_iff.mpr ⟨wB,insert_subset_iff.mpr ⟨hB,singleton_subset_iff.mpr lB⟩⟩⟩
    have n : ({v,w,h,l} : Finset V).card=4 := by simp [vw,vh,vl',wh,wl,lh.symm]
    exact (eq_of_subset_of_card_le sub (by omega)).symm
  have vH := ((hFull h hh).1 v vb vh.symm).symm
  have wH := ((hFull h hh).1 w wB wh.symm).symm
  have hl := (hFull h hh).1 l lB lh.symm
  have bridgeFull (p : V) (pa : p∈A) (q : V) (qb : q∈B) (pq : G.Adj p q) :
      (∀ s∈A,p≠s → G.Adj p s) ∧ ∀ i∈I,G.Adj p i := by
    obtain ⟨pl,ap⟩ := mem_filter.mp pa
    have pz : p≠b := fun e=>S.leftOff.2 (e ▸ pl)
    have b₂ := d2 hc pz (fun e=>not_common far ap e.symm) pq ((mem_filter.mp qb).2).symm
    have qh : q≠h := fun e=>darkNo h hT p pa (e ▸ pq)
    have h₂ := d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) hB)
      (darkNo h hT p pa) pq ((hFull h hh).1 q qb qh.symm).symm
    exact bridge_two_locals_full S hc far even foreign showI pa hB b₂ h₂
  have each (p : V) (pa : p∈A) :
      (∀ s∈A,p≠s → G.Adj p s) ∧ ∀ i∈I,G.Adj p i := by
    by_cases hit : ∃ q∈B,G.Adj p q
    · obtain ⟨q,qb,pq⟩ := hit
      exact bridgeFull p pa q qb pq
    have hi := (degree p l (fun e=>disjoint_left.mp sep (e ▸ pa) lB)).resolve_right low
    have sub := bounds_of_local_color_port S far pa (fun q qb pq=>hit ⟨q,qb,pq⟩)
    change G.neighborFinset p⊆insert a ((A.erase p)∪I) at sub
    exact far_port_full_at_tight_pool pa sub (by omega) hi
  have ac : CompleteOn G (A∪I) := by
    intro x xx y yy xy
    rcases mem_union.mp xx with xa|xi
    · exact (mem_union.mp yy).elim (fun ya=>(each x xa).1 y ya xy) (fun yi=>(each x xa).2 y yi)
    rcases mem_union.mp yy with ya|yi
    · exact ((each y ya).2 x xi).symm
    have a := one_lt_card.mpr ⟨x,xi,y,yi,xy⟩
    omega
  have lNo (q : V) (qw : q∈W) : ¬G.Adj q l := by
    obtain ⟨ql,bq,s,sl,asq,sq⟩ := mem_filter.mp qw
    have sa : s∈A := mem_filter.mpr ⟨sl,asq⟩
    have sqh : q≠h := fun e=>(mem_sdiff.mp hT).2 (e ▸ qw)
    have h2 := d2 hc (fun e=>disjoint_left.mp sep (e ▸ sa) hB)
      (darkNo h hT s sa) sq ((hFull h hh).1 q (wb qw) sqh.symm).symm
    intro ql'
    have l2 := d2 hc (fun e=>disjoint_left.mp sep (e ▸ sa) lB) (darkNo l lT s sa) sq ql'
    have sb : s≠b := fun e=>S.leftOff.2 (e ▸ sl)
    have b₂ := d2 hc sb
      (fun e=>not_common far asq e.symm) sq bq.symm
    let X : Finset V := {b,h,l}
    have whereX : X⊆insert b S.L :=
      insert_subset_iff.mpr ⟨mem_insert_self _ _, insert_subset_iff.mpr
        ⟨mem_insert_of_mem (bL hB),singleton_subset_iff.mpr (mem_insert_of_mem (bL lB))⟩⟩
    have xs : X⊆DistanceTwo G s := insert_subset_iff.mpr
      ⟨b₂,insert_subset_iff.mpr ⟨h2,singleton_subset_iff.mpr l2⟩⟩
    have n := charge s sa whereX xs
    have hnb : b≠h := fun e=>S.leftOff.2 (e.symm ▸ bL hB)
    have lnb : b≠l := fun e=>S.leftOff.2 (e.symm ▸ bL lB)
    have m : X.card=3 := by simp [X,hnb,lnb,lh.symm]
    omega
  refine ⟨ac,v,w,h,l,vw,vh,vl',wh,wl,lh.symm,BQ,vH,wH,hl,?_⟩
  by_cases edge : G.Adj v w
  · exact .inl ⟨edge,p,pa,pv⟩
  right
  have size (q r : V) (qw : q∈W) (_qr : q≠r)
      (qB : q∈B) (nr : ¬G.Adj q r) (B' : B={q,r,h,l}) : 2≤(A.filter (G.Adj q)).card := by
    have high := (degree q l (fun e=>(mem_sdiff.mp lT).2 (e ▸ qw))).resolve_right low
    have sub : G.neighborFinset q⊆insert b (insert h ((A.filter (G.Adj q))∪I)) := by
      intro z zm
      have qz := (mem_neighborFinset G q z).mp zm
      rcases left_boundary S q (bL qB) z qz with za|zb|zl
      · exact (not_common far (za ▸ qz.symm) (mem_filter.mp qB).2).elim
      · exact mem_insert.mpr (.inl zb)
      by_cases az : G.Adj a z
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨zl,az⟩,qz⟩)))
      by_cases bz : G.Adj b z
      · have zb : z∈B := mem_filter.mpr ⟨zl,bz⟩
        have eq : z=q ∨ z=r ∨ z=h ∨ z=l := by simpa [B'] using zb
        rcases eq with e|e|e|e
        · exact (qz.ne e.symm).elim
        · exact (nr (e ▸ qz)).elim
        · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
        exact (lNo q qw (e ▸ qz)).elim
      exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨zl,az,bz⟩)))
    have n := (card_le_card sub).trans (card_insert_le b _)
    have k := card_insert_le h ((A.filter (G.Adj q))∪I)
    have u := card_union_le (A.filter (G.Adj q)) I
    rw [card_neighborFinset_eq_degree] at n
    omega
  have sv := size v w vv vw vb edge BQ
  have sw := size w v wW wv wB (fun h=>edge h.symm) (by
    rw [BQ]; ext x; simp [or_comm,or_left_comm,or_assoc])
  obtain ⟨x,xx⟩ := card_pos.mp (show 0<(A.filter (G.Adj v)).card by omega)
  obtain ⟨u,uu,y,yy,uy⟩ := one_lt_card.mp (show 1<(A.filter (G.Adj w)).card by omega)
  by_cases eq : x=u
  · exact ⟨x,(mem_filter.mp xx).1,y,(mem_filter.mp yy).1,
      fun e=>uy (eq.symm.trans e),(mem_filter.mp xx).2,(mem_filter.mp yy).2.symm⟩
  exact ⟨x,(mem_filter.mp xx).1,u,(mem_filter.mp uu).1,eq,(mem_filter.mp xx).2,(mem_filter.mp uu).2.symm⟩

#print axioms four_a_bridge_one_inner_geometry
end Graffiti189LongestPath.CrossSaturation.Split.Five
