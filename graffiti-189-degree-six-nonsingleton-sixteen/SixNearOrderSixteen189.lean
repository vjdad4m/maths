import SixDistanceThreeEighteen189
import TwoCutDistanceCaps189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_connected shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected two_local_counts from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private degree_le_shore degree_le_shore_add_one Vis vis_sub vis_card_ge_two from AdjacentCutFiveComponents189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private rooted_side inside_lower_of_boundary from AdjacentCutFiveMixedRouteSmall189
open private dark_degree from SixCutLowSingleton189
open private d2 from CrossSaturation189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem two_distinct_ports (ab : a≠b) (conn : DeletionConnected G) (C : Cmp G a b)
    (big : 2≤(Shore C).card) :
    ∃ x∈Shore C,∃ y∈Shore C,x≠y ∧ G.Adj a x ∧ G.Adj b y := by
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,yc,by'⟩ := shore_hit_b ab conn C
  by_cases eq : x=y
  · subst y
    obtain ⟨z,zv,zx⟩ := exists_ne_of_one_lt_card (s:=Vis C) (by have k := vis_card_ge_two ab conn C big; omega) x
    obtain ⟨zc,az|bz⟩ := mem_filter.mp zv
    · exact ⟨z,zc,x,xc,zx,az,by'⟩
    exact ⟨x,xc,z,zc,zx.symm,ax,bz⟩
  exact ⟨x,xc,y,yc,eq,ax,by'⟩

private theorem near_inside_four (ab : a≠b) (C : Cmp G a b)
    {z : V} (zc : z∈Shore C) (hi : 6≤G.degree z) :
    4≤(inside G (Shore C) z).card := by
  have q := inside_lower_of_boundary (G:=G) (Shore C) {a,b} (u:=z)
    (fun w zw=>by
      rcases shore_closed C z zc w zw with rfl|rfl|h
      · exact .inr (by simp)
      · exact .inr (by simp)
      exact .inl h)
  rw [card_insert_of_not_mem (by simpa using ab),card_singleton] at q
  omega

private theorem common_of_internal_four (C : Cmp G a b)
    {z : V} (zc : z∈Shore C) (hi : 6≤G.degree z) (four : (inside G (Shore C) z).card=4) :
    G.Adj a z ∧ G.Adj b z := by
  have upper {t : V} (h : ∀ w,G.Adj z w → w∈Shore C ∨ w=t) : G.degree z≤5 := by
    have q := inside_lower_of_boundary (G:=G) (Shore C) {t} (u:=z)
      (fun w zw=>(h w zw).imp id mem_singleton.mpr)
    rw [card_singleton,four] at q
    exact q
  constructor
  · by_contra no
    have k := upper (t:=b) (fun w zw=>by
      rcases shore_closed C z zc w zw with rfl|rfl|w
      · exact (no zw.symm).elim
      · exact .inr rfl
      exact .inl w)
    omega
  by_contra no
  have k := upper (t:=a) (fun w zw=>by
    rcases shore_closed C z zc w zw with rfl|rfl|w
    · exact .inr rfl
    · exact (no zw.symm).elim
    exact .inl w)
  omega

private theorem low_card (S : Finset V)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) :
    (S.filter (fun z=>G.degree z<6)).card≤1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra ne
  have a := (mem_filter.mp hx).2
  have b := (mem_filter.mp hy).2
  rcases degree x y ne with q|q <;> omega

private theorem high_near_shore_size (C : Cmp G a b) (big : 2≤(Shore C).card)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) : 5≤(Shore C).card := by
  have more : 1<(Shore C).card := by omega
  obtain ⟨x,xc,y,yc,xy⟩ := one_lt_card.mp more
  have dx := degree_le_shore_add_one C xc
  have dy := degree_le_shore_add_one C yc
  rcases degree x y xy with h|h <;> omega

private theorem visible_at_five_or_six (C : Cmp G a b) (size : (Shore C).card≤6)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) :
    (Shore C).card-1≤(Vis C).card := by
  have s : Shore C\Vis C⊆(Shore C).filter (fun z=>G.degree z<6) := by
    intro z hz
    obtain ⟨zc,zn⟩ := mem_sdiff.mp hz
    have k := card_le_card (dark_degree C zc zn)
    rw [card_neighborFinset_eq_degree] at k
    have q := card_erase_add_one zc
    exact mem_filter.mpr ⟨zc,by omega⟩
  have c := card_le_card s
  rw [card_sdiff (vis_sub C)] at c
  have q := low_card (Shore C) degree
  omega

private theorem nonadjacent_high_inside_two (hc : G.Connected) (K : Cmp G a b)
    (size : (Shore K).card≤9) {x z : V} (xk : x∈Shore K) (zk : z∈Shore K)
    (xz : x≠z) (no : ¬G.Adj x z)
    (dx : 4≤(inside G (Shore K) x).card) (dz : 4≤(inside G (Shore K) z).card) :
    z∈DistanceTwo G x := by
  classical
  let A := inside G (Shore K) x
  let B := inside G (Shore K) z
  let W := ((Shore K).erase x).erase z
  have sA : A⊆W := by
    intro u hm
    obtain ⟨uk,xu⟩ := mem_filter.mp hm
    exact mem_erase.mpr ⟨fun e=>no (e ▸ xu),mem_erase.mpr ⟨xu.ne.symm,uk⟩⟩
  have sB : B⊆W := by
    intro u hm
    obtain ⟨uk,zu⟩ := mem_filter.mp hm
    exact mem_erase.mpr ⟨zu.ne.symm,mem_erase.mpr ⟨fun e=>no (e ▸ zu).symm,uk⟩⟩
  have meet : (A∩B).Nonempty := by
    by_contra! nil
    have apart : Disjoint A B := by rw [disjoint_iff_inter_eq_empty]; exact not_nonempty_iff_eq_empty.mp nil
    have h := two_local_counts A B apart W sA sB
    have w : W.card≤7 := by
      change (((Shore K).erase x).erase z).card≤7
      rw [card_erase_of_mem (mem_erase.mpr ⟨xz.symm,zk⟩),card_erase_of_mem xk]
      omega
    change 4≤A.card at dx
    change 4≤B.card at dz
    omega
  obtain ⟨u,hu⟩ := meet
  exact d2 hc xz no (mem_filter.mp (mem_inter.mp hu).1).2 (mem_filter.mp (mem_inter.mp hu).2).2.symm

private theorem high_local_improvement (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (size : (Shore D).card≤9)
    (cv : 4≤(Vis C).card)
    (room : (Shore D).card=9 ∨ ((Shore D).card=8 ∧ ∀ z∈Shore D,6≤G.degree z))
    {x : V} (xd : x∈Shore D) (hi : 6≤G.degree x) :
    5≤(inside G (Shore D) x).card := by
  classical
  by_contra no
  have d4 := near_inside_four ab D xd hi
  have four : (inside G (Shore D) x).card=4 := by omega
  obtain ⟨ax,bx⟩ := common_of_internal_four D xd hi four
  let F := (Shore D).erase x\inside G (Shore D) x
  let B := F.filter (fun z=>6≤G.degree z)
  have subI : inside G (Shore D) x⊆(Shore D).erase x :=
    fun _ h=>mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
  have fsz : F.card=(Shore D).card-1-4 := by
    change ((Shore D).erase x\inside G (Shore D) x).card=_
    rw [card_sdiff subI,card_erase_of_mem xd,four]
  have b3 : 3≤B.card := by
    rcases room with nine|⟨eight,all⟩
    · have lo := low_card F degree
      have e : B∪F.filter (fun z=>G.degree z<6)=F := by
        ext z
        by_cases zf : z∈F
        · by_cases zh : 6≤G.degree z
          · simp [B,zf,zh]
          · have zl : G.degree z<6 := by omega
            simp [B,zf,zh,zl]
        · simp [B,zf]
      have p := card_union_le B (F.filter (fun z=>G.degree z<6))
      rw [e] at p
      omega
    have q : F⊆B := fun z h=>mem_filter.mpr
      ⟨h,all z (mem_erase.mp (mem_sdiff.mp h).1).2⟩
    have j := card_le_card q
    omega
  have bsub : B⊆DistanceTwo G x := by
    intro z b
    obtain ⟨f,zh⟩ := mem_filter.mp b
    obtain ⟨near,far⟩ := mem_sdiff.mp f
    obtain ⟨zx,zd⟩ := mem_erase.mp near
    exact nonadjacent_high_inside_two hc D size xd zd zx.symm
      (fun xz=>far (mem_filter.mpr ⟨zd,xz⟩)) d4 (near_inside_four ab D zd zh)
  have vsub : Vis C⊆DistanceTwo G x := by
    intro z zz
    obtain ⟨zc,za|zb⟩ := mem_filter.mp zz
    · have ne : x≠z := fun eq=>disjoint_left.mp (shore_disjoint cd) zc (eq ▸ xd)
      have no : ¬G.Adj x z := by
        intro xz
        rcases shore_closed D x xd z xz with e|e|e
        · exact (shore_off C).1 (e ▸ zc)
        · exact (shore_off C).2 (e ▸ zc)
        exact disjoint_left.mp (shore_disjoint cd) zc e
      exact d2 hc ne no ax.symm za
    have ne : x≠z := fun eq=>disjoint_left.mp (shore_disjoint cd) zc (eq ▸ xd)
    have no : ¬G.Adj x z := by
      intro xz
      rcases shore_closed D x xd z xz with e|e|e
      · exact (shore_off C).1 (e ▸ zc)
      · exact (shore_off C).2 (e ▸ zc)
      exact disjoint_left.mp (shore_disjoint cd) zc e
    exact d2 hc ne no bx.symm zb
  have h : Disjoint (Vis C) B := (shore_disjoint cd).mono (vis_sub C)
    (fun _ b=>(mem_erase.mp (mem_sdiff.mp (mem_filter.mp b).1).1).2)
  have q := two_local_counts _ _ h _ vsub bsub
  have k := distanceTwo_le_of_even 6 x (even x)
  omega

private theorem join_near_shore_to_middle (ab : a≠b)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c2 : 2≤(Shore C).card)
    (free : ∀ u∈Shore C,∀ v∈Shore C,6≤G.degree u → 6≤G.degree v →
      (Shore C).card≤(inside G (Shore C) u).card+(inside G (Shore C) v).card)
    {ya yb : V}
    (aya : G.Adj a ya) (byb : G.Adj b yb) (M : RouteOn G (Shore D) ya yb) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨xa,xaC,xb,xbC,xab,axa,bxb⟩ := two_distinct_ports ab conn C c2
  obtain ⟨s,t,port,R⟩ := rooted_side (Shore C) (fun z=>G.Adj a z ∨ G.Adj b z)
    (fun z=>6≤G.degree z) (shore_connected C)
    ⟨xa,xaC,xb,xbC,xab,.inl axa,.inr bxb⟩
    (fun u _ v _ uv=>degree u v uv) (fun u uc v vc _ _ hu hv=>free u uc v vc hu hv)
  have finish {g h i j : V} (gh : g≠h)
      (gC : g∉Shore C) (hC : h∉Shore C) (gD : g∉Shore D) (hD : h∉Shore D)
      (ends : ∀ {z : V},z≠g → z≠h → z∈Shore C ∨ z∈Shore D)
      (route : RouteOn G (Shore D) i j) (gs : G.Adj g s) (gi : G.Adj g i) (hj : G.Adj h j) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    have dis : Disjoint (insert g (Shore C)) (insert h (Shore D)) := by
      apply disjoint_left.mpr
      intro z zc zd
      rcases mem_insert.mp zc with rfl|zc
      · exact (mem_insert.mp zd).elim gh gD
      rcases mem_insert.mp zd with rfl|zd
      · exact hC zc
      exact disjoint_left.mp (shore_disjoint cd) zc zd
    obtain ⟨q,qq,qs⟩ := (R.reverse.suffix gs.symm gC).join (route.suffix hj.symm hD) dis gi
    refine ⟨t,h,q,qq,fun z=>(qs z).mpr ?_⟩
    by_cases e : z=g
    · simp [e]
    by_cases f : z=h
    · simp [f]
    rcases ends e f with k|k <;> simp [k]
  rcases port with pa|pb
  · exact finish ab (shore_off C).1 (shore_off C).2 (shore_off D).1 (shore_off D).2 cover M pa aya byb
  exact finish ab.symm (shore_off C).2 (shore_off C).1 (shore_off D).2 (shore_off D).1
    (fun zb za=>cover za zb) M.reverse pb byb aya

/-- At order at most sixteen, degree-six two-separators whose shores are
both nonsingletons give a spanning path, for adjacent or nonadjacent cuts. -/
theorem traceable_at_six_nonsingleton_shores_order_sixteen
    (hc : G.Connected) (ab : a≠b) (even : ∀ x,(EvenFrom G x).card≤7)
    (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b))
    (n : Fintype.card V≤16) (ns : ∀ K : Cmp G a b,2≤(Shore K).card) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have run (K L : Cmp G a b) (kl : K≠L)
      (cov : ∀ {z : V},z≠a → z≠b → z∈Shore K ∨ z∈Shore L)
      (all : ∀ z∈Shore L,6≤G.degree z) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    have K5 := high_near_shore_size K (ns K) degree
    have L5 := high_near_shore_size L (ns L) degree
    have sum := shore_sum_with_cover ab kl cov
    have free (u : V) (uk : u∈Shore K) (v : V) (vk : v∈Shore K)
        (uh : 6≤G.degree u) (vh : 6≤G.degree v) :
        (Shore K).card≤(inside G (Shore K) u).card+(inside G (Shore K) v).card := by
      have up := near_inside_four ab K uk uh
      have vp := near_inside_four ab K vk vh
      by_cases sm : (Shore K).card≤8
      · omega
      have size : (Shore K).card=9 := by omega
      have cv := visible_at_five_or_six L (by omega) degree
      have up := high_local_improvement hc ab even degree kl.symm (by omega) (by omega) (.inl size) uk uh
      have vp := high_local_improvement hc ab even degree kl.symm (by omega) (by omega) (.inl size) vk vh
      omega
    have mid (u : V) (ul : u∈Shore L) (v : V) (vl : v∈Shore L) :
        (Shore L).card+1≤(inside G (Shore L) u).card+(inside G (Shore L) v).card := by
      have up := near_inside_four ab L ul (all u ul)
      have vp := near_inside_four ab L vl (all v vl)
      by_cases sm : (Shore L).card≤7
      · omega
      have room : (Shore L).card=9 ∨ ((Shore L).card=8 ∧ ∀ z∈Shore L,6≤G.degree z) := by
        by_cases s : (Shore L).card=9
        · exact .inl s
        exact .inr ⟨by omega,all⟩
      have cv := visible_at_five_or_six K (by omega) degree
      have up := high_local_improvement hc ab even degree kl (by omega) (by omega) room ul (all u ul)
      have vp := high_local_improvement hc ab even degree kl (by omega) (by omega) room vl (all v vl)
      omega
    obtain ⟨u,ul,v,vl,uv,au,bv⟩ := two_distinct_ports ab conn L (ns L)
    have R := terminal_route_on_of_local_ore (Shore L) ul vl uv (fun w wl x xl _ _=>mid w wl x xl)
    exact join_near_shore_to_middle ab conn degree kl cov (ns K) free au bv R
  by_cases all : ∀ z∈Shore D,6≤G.degree z
  · exact run C D cd cover all
  push_neg at all
  obtain ⟨w,wd,wl⟩ := all
  apply run D C cd.symm (fun za zb=>(cover za zb).symm)
  intro z zc
  have ne : z≠w := fun e=>disjoint_left.mp (shore_disjoint cd) zc (e.symm ▸ wd)
  exact (degree z w ne).resolve_right (by omega)

#print axioms traceable_at_six_nonsingleton_shores_order_sixteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
