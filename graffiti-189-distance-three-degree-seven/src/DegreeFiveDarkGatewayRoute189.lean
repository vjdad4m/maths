import DegreeFiveGatewayDarkBounds189
import DegreeFiveAlternatingLeafStart189
import SmallDenseRoute189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- A dark block of at most five vertices, joined through its gateway and
with at most three contacts to the terminal cut, can be traversed out to
one of these contacts. The degree premise is measured in the original graph. -/
theorem route_through_dark_gateway_block {T : Finset V} {z b : V}
    (cap : T.card≤5) (bc : (T.filter (G.Adj b)).card≤3)
    (touch : ∃ t∈T,G.Adj b t)
    (bound : ∀ t∈T,∀ u,G.Adj t u → u=z ∨ u=b ∨ u∈T)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y) :
    ∃ r t,G.Adj b t ∧ RouteOn G T r t := by
  classical
  let B := T.filter (G.Adj b)
  obtain ⟨t,tT,bt⟩ := touch
  have tB : t∈B := mem_filter.mpr ⟨tT,bt⟩
  have all (x : V) (xt : x∈T) : G.neighborFinset x⊆insert z (insert b (T.erase x)) := by
    intro v vn
    have xv := (mem_neighborFinset G x v).mp vn
    rcases bound x xt v xv with e|e|vt
    · exact mem_insert.mpr (.inl e)
    · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨xv.ne.symm,vt⟩))
  have noB (x : V) (xt : x∈T) (bx : ¬G.Adj b x) :
      G.neighborFinset x⊆insert z (T.erase x) := by
    intro v vn
    have xv := (mem_neighborFinset G x v).mp vn
    rcases bound x xt v xv with e|e|vt
    · exact mem_insert.mpr (.inl e)
    · exact (bx (e ▸ xv.symm)).elim
    exact mem_insert_of_mem (mem_erase.mpr ⟨xv.ne.symm,vt⟩)
  have upper (x : V) (xt : x∈T) : G.degree x≤T.card+1 := by
    have c := (card_le_card (all x xt)).trans (card_insert_le z (insert b (T.erase x)))
    have d := card_insert_le b (T.erase x)
    rw [card_neighborFinset_eq_degree] at c
    rw [card_erase_of_mem xt] at d
    have hpos : 0 < T.card := card_pos.mpr ⟨x,xt⟩
    omega
  have oneOr : T.card=1 ∨ 4≤T.card := by
    by_cases ss : T.card=1
    · exact .inl ss
    right
    apply Classical.byContradiction
    intro n
    have pos := card_pos.mpr ⟨t,tT⟩
    obtain ⟨u,ut,v,vt,uv⟩ := one_lt_card.mp (show 1<T.card by omega)
    have du := upper u ut
    have dv := upper v vt
    exact (degree u v uv).elim (fun h=>by omega) (fun h=>by omega)
  rcases oneOr with one|large
  · have eq : T={t} := by
      exact (eq_of_subset_of_card_le (singleton_subset_iff.mpr tT) (by rw [card_singleton,one])).symm
    exact ⟨t,t,bt,eq.symm ▸ RouteOn.singleton⟩
  by_cases four : T.card=4
  · have univ (x : V) (xt : x∈T) (hi : 5≤G.degree x) :
        ∀ y∈T,x≠y → G.Adj x y := by
      have sz : (insert z (insert b (T.erase x))).card≤5 := by
        have c := card_insert_le z (insert b (T.erase x))
        have d := card_insert_le b (T.erase x)
        rw [card_erase_of_mem xt,four] at d
        omega
      have eq : G.neighborFinset x=insert z (insert b (T.erase x)) :=
        eq_of_subset_of_card_le (all x xt) (by rw [card_neighborFinset_eq_degree]; omega)
      intro y yt ne
      exact (mem_neighborFinset G x y).mp (eq.symm ▸
        mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨ne.symm,yt⟩)))
    have cl : CompleteOn G T := fun x xs y ys ne=>(degree x y ne).elim
      (fun h=>univ x xs h y ys ne) (fun h=>(univ y ys h x xs ne.symm).symm)
    obtain ⟨r,p,pp,ps⟩ := rooted_path_in_clique T cl tT
    have q : RouteOn G T t r := ⟨p,pp,ps⟩
    exact ⟨r,t,bt,q.reverse⟩
  have five : T.card=5 := by omega
  let N := T\B
  let H := N.filter (fun x=>5≤G.degree x)
  have hes : H⊆N := filter_subset _ _
  have nts : N⊆T := sdiff_subset
  have bts : B⊆T := filter_subset _ _
  have tSize : N.card+B.card=T.card := card_sdiff_add_card_eq_card bts
  have nHigh : 2≤N.card := by
    change B.card≤3 at bc
    omega
  have hCover (x : V) (xh : x∈H) : ∀ y∈T,x≠y → G.Adj x y := by
    obtain ⟨xn,hi⟩ := mem_filter.mp xh
    obtain ⟨xt,notB⟩ := mem_sdiff.mp xn
    have bx : ¬G.Adj b x := fun q=>notB (mem_filter.mpr ⟨xt,q⟩)
    have co := card_insert_le z (T.erase x)
    rw [card_erase_of_mem xt,five] at co
    have eq : G.neighborFinset x=insert z (T.erase x) :=
      eq_of_subset_of_card_le (noB x xt bx) (by rw [card_neighborFinset_eq_degree]; omega)
    intro y yt ne
    exact (mem_neighborFinset G x y).mp
      (eq.symm ▸ mem_insert_of_mem (mem_erase.mpr ⟨ne.symm,yt⟩))
  have low (x : V) (xn : x∈N\H) : ¬5≤G.degree x :=
    fun hi=>(mem_sdiff.mp xn).2 (mem_filter.mpr ⟨(mem_sdiff.mp xn).1,hi⟩)
  have nl : (N\H).card≤1 := by
    apply Classical.byContradiction
    intro h
    obtain ⟨u,un,v,vn,uv⟩ := one_lt_card.mp (show 1<(N\H).card by omega)
    exact (degree u v uv).elim (low u un) (low v vn)
  have nSum : (N\H).card+H.card=N.card := card_sdiff_add_card_eq_card hes
  obtain ⟨u,uh⟩ := card_pos.mp (show 0<H.card by omega)
  by_cases h2 : 2≤H.card
  · let L := T\H
    have sep : Disjoint H L := disjoint_left.mpr (fun w wh wl=>(mem_sdiff.mp wl).2 wh)
    have cl : CompleteOn G H := fun x xh y yh ne=>hCover x xh y (nts (hes yh)) ne
    have cross (x : V) (xh : x∈H) (y : V) (yl : y∈L) : G.Adj x y :=
      hCover x xh y (mem_sdiff.mp yl).1 (fun e=>(mem_sdiff.mp yl).2 (e ▸ xh))
    have lt : t∈L := mem_sdiff.mpr ⟨tT,fun h=>(mem_sdiff.mp (hes h)).2 tB⟩
    have sum : L.card+H.card=T.card := card_sdiff_add_card_eq_card (hes.trans nts)
    obtain ⟨r,p⟩ := route_clique_join_end_leaf_allow_leaf_start sep cl cross (by omega) uh lt
    have union : H∪L=T := union_sdiff_of_subset (hes.trans nts)
    exact ⟨r,t,bt,union ▸ p⟩
  have h1 : H.card=1 := by omega
  have n2 : N.card=2 := by omega
  have b3 : B.card=3 := by omega
  have wpos : 0<(N\H).card := by omega
  obtain ⟨w,wn⟩ := card_pos.mp wpos
  have loww := low w wn
  have wh : w∉H := (mem_sdiff.mp wn).2
  have un : u∈N := hes uh
  have wN : w∈N := (mem_sdiff.mp wn).1
  have wu : w≠u := fun e=>wh (e.symm ▸ uh)
  have nEq : N={w,u} := by
    exact (eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨wN,singleton_subset_iff.mpr un⟩)
      (by rw [n2]; simp [wu])).symm
  have subset (v : V) (vb : v∈B) : ∃ c∈B,G.Adj v c := by
    apply Classical.byContradiction
    intro no
    have vt := bts vb
    have vw : v≠w := fun e=>(mem_sdiff.mp wN).2 (e ▸ vb)
    have v5 := (degree v w vw).resolve_right loww
    have sub : G.neighborFinset v⊆insert z (insert b N) := by
      intro k kv
      have vk := (mem_neighborFinset G v k).mp kv
      rcases bound v vt k vk with e|e|kt
      · exact mem_insert.mpr (.inl e)
      · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
      exact mem_insert_of_mem (mem_insert_of_mem
        (mem_sdiff.mpr ⟨kt,fun kb=>no ⟨k,kb,vk⟩⟩))
    have e := (card_le_card sub).trans (card_insert_le z (insert b N))
    have j := card_insert_le b N
    rw [card_neighborFinset_eq_degree] at e
    omega
  obtain ⟨s,sb,q,qb,p⟩ := three_finset_spanning_path B b3 subset
  have uOff : u∉B := (mem_sdiff.mp un).2
  have wOff : w∉B := (mem_sdiff.mp wN).2
  have us : u≠s := fun e=>uOff (e.symm ▸ sb)
  have p₂ := p.prefix (hCover u uh s (bts sb) us) uOff
  have p₃ := p₂.prefix (hCover u uh w (nts wN) wu.symm).symm
    (fun m=>(mem_insert.mp m).elim wu wOff)
  have eq : insert w (insert u B)=T := by
    have c : B∪N=T := union_sdiff_of_subset bts
    rw [←c,nEq]
    ext v
    simp [or_comm,or_left_comm,or_assoc]
  exact ⟨w,q,(mem_filter.mp qb).2,eq ▸ p₃⟩

#print axioms route_through_dark_gateway_block
end Graffiti189LongestPath.CrossSaturation.Split.Five
