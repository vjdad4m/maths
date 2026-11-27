import CutExtraction189
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.VecNotation

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Three nonintersecting connected shores of deletion of a single vertex. -/
structure ThreeShores (G : SimpleGraph V) (c : V) where
  H : Fin 3 → Finset V
  dis : ∀ i j, i≠j → Disjoint (H i) (H j)
  off : ∀ i,c∉H i
  closed : ∀ i,∀ x∈H i,∀ y,G.Adj x y → y=c ∨ y∈H i
  joined : ∀ i,(G.induce (↑(H i) : Set V)).Connected
  hit : ∀ i,∃ x∈H i,G.Adj c x

namespace ThreeShores
variable {c : V} (S : ThreeShores G c)
def ports (i : Fin 3) := (S.H i).filter (G.Adj c)
noncomputable def innerTwo (i : Fin 3) := (S.H i) ∩ DistanceTwo G c

private theorem d2 {x y z : V} (hc : G.Connected) (xz : x≠z)
    (non : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    z∈DistanceTwo G x := by
  classical
  have h := hc.one_lt_dist_of_ne_of_not_adj xz non
  have le := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at le
  simp [DistanceTwo, show G.dist x z=2 by omega]

private theorem cross_dis {i j : Fin 3} (ne : i≠j) {x y : V}
    (xi : x∈S.H i) (yj : y∈S.H j) : x≠y ∧ ¬G.Adj x y := by
  have yn : y∉S.H i := fun h=>disjoint_left.mp (S.dis i j ne) h yj
  exact ⟨fun h=>yn (h ▸ xi),fun h=>(S.closed i x xi y h).elim
    (fun e=>S.off j (e ▸ yj)) yn⟩

private theorem across_port_subset (hc : G.Connected) {i j : Fin 3} (ne : i≠j)
    {x : V} (xi : x∈S.ports i) : S.ports j ⊆ DistanceTwo G x := by
  intro y yj
  obtain ⟨xi,cx⟩ := mem_filter.mp xi
  obtain ⟨yj,cy⟩ := mem_filter.mp yj
  have h := cross_dis S ne xi yj
  exact d2 hc h.1 h.2 cx.symm cy

private theorem across_cap (hc : G.Connected) (d : ∀ x, (DistanceTwo G x).card≤4)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    (S.ports j).card+(S.ports k).card≤4 := by
  obtain ⟨x,xi,cx⟩ := S.hit i
  have port : x∈S.ports i := mem_filter.mpr ⟨xi,cx⟩
  have sub := union_subset (across_port_subset S hc ij port) (across_port_subset S hc ik port)
  have n := card_le_card sub
  have djk : Disjoint (S.ports j) (S.ports k) := (S.dis j k jk).mono (filter_subset (G.Adj c) (S.H j)) (filter_subset (G.Adj c) (S.H k))
  rw [card_union_of_disjoint djk] at n
  exact n.trans (d x)

private theorem internal_cap (d : ∀ x, (DistanceTwo G x).card≤4)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    (S.innerTwo i).card+(S.innerTwo j).card+(S.innerTwo k).card≤4 := by
  have pair (p q : Fin 3) (pq : p≠q) : Disjoint (S.innerTwo p) (S.innerTwo q) :=
    (S.dis _ _ pq).mono inter_subset_left inter_subset_left
  have sub (p : Fin 3) : S.innerTwo p ⊆ DistanceTwo G c := inter_subset_right
  have cnt := card_le_card (union_subset (union_subset (sub i) (sub j)) (sub k))
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨pair i k ik,pair j k jk⟩),
    card_union_of_disjoint (pair i j ij)] at cnt
  exact cnt.trans (d c)

private theorem high_port_cost (hc : G.Connected) {i : Fin 3} {x : V}
    (xp : x∈S.ports i) (high : 4≤G.degree x) :
    4≤(S.ports i).card+(S.innerTwo i).card := by
  classical
  obtain ⟨xi,cx⟩ := mem_filter.mp xp
  have inc : G.neighborFinset x ⊆ insert c (((S.ports i).erase x) ∪ S.innerTwo i) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed i x xi y xy with rfl|yi
    · simp
    apply mem_insert_of_mem
    by_cases cy : G.Adj c y
    · exact mem_union_left _ (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yi,cy⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨yi,d2 hc (fun e=>S.off i (e.symm ▸ yi)) cy cx xy⟩)
  have deg := card_le_card inc
  rw [card_neighborFinset_eq_degree] at deg
  have c1 := card_insert_le c ((S.ports i).erase x ∪ S.innerTwo i)
  have c2 := card_union_le ((S.ports i).erase x) (S.innerTwo i)
  rw [card_erase_of_mem xp] at c2
  have pos := card_pos.mpr ⟨x,xp⟩
  omega

private theorem all_ports_if_no_inner (hc : G.Connected) (i : Fin 3)
    (none : (S.innerTwo i).card=0) : S.H i ⊆ S.ports i := by
  classical
  obtain ⟨x,xi,cx⟩ := S.hit i
  intro y yi
  let U : Set V := ↑(S.H i)
  obtain ⟨p⟩ := (S.joined i).preconnected (⟨x,xi⟩ : U) ⟨y,yi⟩
  have step {u v : U} (w : (G.induce U).Walk u v) :
      G.Adj c u.val → G.Adj c v.val := by
    induction w with
    | nil => exact id
    | @cons u z v uz q ih =>
      intro cu
      apply ih
      by_contra bad
      have zz : z.val ∈ S.H i := z.property
      have cz : c≠z.val := fun e=>S.off i ((congrArg (fun u=>u∈S.H i) e.symm).mp zz)
      have f := d2 hc cz bad cu (show G.Adj u.val z.val from uz)
      have mf : z.val∈S.innerTwo i := mem_inter.mpr ⟨z.property,f⟩
      have p := card_pos.mpr ⟨_,mf⟩
      omega
  exact mem_filter.mpr ⟨yi,step p cx⟩

private theorem no_low_shore (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (low : ¬ ∃ x∈S.ports i, 4≤G.degree x) : False := by
  classical
  have d (x : V) := distanceTwo_le_of_even 4 x (even x)
  obtain ⟨x,xi,cx⟩ := S.hit i
  have xp : x∈S.ports i := mem_filter.mpr ⟨xi,cx⟩
  have lx : ¬4≤G.degree x := fun h=>low ⟨x,xp,h⟩
  have p1 : (S.ports i).card=1 := by
    have eq : S.ports i = {x} := by
      apply Subset.antisymm
      · intro y yp
        by_contra bad
        have n : x≠y := fun e=>bad (by simp [e])
        rcases degree x y n with l|r
        · exact lx l
        · exact low ⟨y,yp,r⟩
      exact singleton_subset_iff.mpr xp
    simp [eq]
  have hport (l : Fin 3) (il : i≠l) : 4≤(S.ports l).card+(S.innerTwo l).card := by
    obtain ⟨y,yl,cy⟩ := S.hit l
    have ne := (cross_dis S il xi yl).1
    exact high_port_cost S hc (mem_filter.mpr ⟨yl,cy⟩) ((degree x y ne).resolve_left lx)
  have jh := hport j ij
  have kh := hport k ik
  have ac := across_cap S hc d i j k ij ik jk
  have dc := internal_cap S d i j k ij ik jk
  have qi : (S.innerTwo i).card=0 := by omega
  have pair : (S.ports j).card+(S.ports k).card=4 := by omega
  have ccj : (S.ports j).card+(S.innerTwo j).card=4 := by omega
  have cck : (S.ports k).card+(S.innerTwo k).card=4 := by omega
  have xonly : S.H i={x} := by
    have n := card_le_card (all_ports_if_no_inner S hc i qi)
    exact (eq_of_subset_of_card_le (singleton_subset_iff.mpr xi) (by simpa using (show (S.H i).card ≤ 1 by omega))).symm
  have radix (z : V) : G.dist x z≤3 := by
    by_contra bad
    have ds : Disjoint (S.ports j) (S.ports k) := (S.dis j k jk).mono (filter_subset (G.Adj c) (S.H j)) (filter_subset (G.Adj c) (S.H k))
    have sub := union_subset (across_port_subset S hc ij xp) (across_port_subset S hc ik xp)
    have n := card_le_card sub
    rw [card_union_of_disjoint ds,pair] at n
    have far : 4≤G.dist x z := by omega
    have e := distanceTwo_add_two_le_even_of_far hc far
    have bound := even x
    omega
  have closedX (u : V) (us : u∈({x} : Finset V)) (v : V) (uv : G.Adj u v) :
      v=c ∨ v=c ∨ v∈({x} : Finset V) := by
    have eu : u=x := mem_singleton.mp us
    subst u
    rcases S.closed i x xi v uv with rfl|vi
    · exact .inl rfl
    · exact .inr (.inr (by simpa [xonly] using vi))
  have all (l : Fin 3) (il : i≠l) : S.H l ⊆ S.ports l ∪ S.innerTwo l := by
    intro z zl
    by_cases cz : G.Adj c z
    · exact mem_union_left _ (mem_filter.mpr ⟨zl,cz⟩)
    have ne := (cross_dis S il xi zl).1
    have miss : z∉({x} : Finset V) := by simp [ne.symm]
    have d3 := radix z
    have cp := cross_metric (a:=c) (b:=c) {x} hc (mem_singleton_self _) miss closedX
    have one := dist_eq_one_iff_adj.mpr cx.symm
    rw [min_self,one] at cp
    have cne : c≠z := fun e=>S.off l (e.symm ▸ zl)
    have ge := hc.one_lt_dist_of_ne_of_not_adj cne cz
    exact mem_union_right _ (mem_inter.mpr ⟨zl,by simp [DistanceTwo,show G.dist c z=2 by omega]⟩)
  have full (l : Fin 3) (il : i≠l) (rhs : (S.ports l).card+(S.innerTwo l).card=4) :
      (S.ports l).card=4 := by
    have cH : (S.H l).card≤4 := ((card_le_card (all l il)).trans (card_union_le _ _)).trans_eq rhs
    have inc : S.H l ⊆ S.ports l := by
      intro y yl
      apply Classical.byContradiction
      intro bad
      have cy : ¬G.Adj c y := by
        intro e
        apply bad
        exact mem_filter.mpr ⟨yl,e⟩
      have incN : G.neighborFinset y ⊆ (S.H l).erase y := by
        intro z zn
        have yz := (mem_neighborFinset G y z).mp zn
        rcases S.closed l y yl z yz with rfl|zl
        · exact (cy yz.symm).elim
        · exact mem_erase.mpr ⟨yz.ne.symm,zl⟩
      have n := card_le_card incN
      rw [card_neighborFinset_eq_degree,card_erase_of_mem yl] at n
      have h := (degree x y (cross_dis S il xi yl).1).resolve_left lx
      omega
    have e : S.H l=S.ports l := Subset.antisymm inc (filter_subset _ _)
    have q : (S.innerTwo l).card=0 := by
      apply card_eq_zero.mpr
      ext z
      simp only [not_mem_empty,iff_false]
      intro zz
      have port := inc (mem_inter.mp zz).1
      have one := dist_eq_one_iff_adj.mpr (mem_filter.mp port).2
      have two := (mem_filter.mp (mem_inter.mp zz).2).2
      omega
    omega
  have fj := full j ij ccj
  have fk := full k ik cck
  omega

include S in
/-- In the degree-four case an articulation cannot separate three
nonempty connected components. -/
theorem impossible (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v) : False := by
  classical
  by_cases low : ∃ i, ¬∃ x∈S.ports i, 4≤G.degree x
  · obtain ⟨i,il⟩ := low
    fin_cases i
    · exact no_low_shore S hc even degree 0 1 2 (by decide) (by decide) (by decide) il
    · exact no_low_shore S hc even degree 1 0 2 (by decide) (by decide) (by decide) il
    · exact no_low_shore S hc even degree 2 0 1 (by decide) (by decide) (by decide) il
  push_neg at low
  have high (i : Fin 3) : 4≤(S.ports i).card+(S.innerTwo i).card := by
    obtain ⟨x,px,dx⟩ := low i
    exact high_port_cost S hc px dx
  have d (x : V) := distanceTwo_le_of_even 4 x (even x)
  have c0 := across_cap S hc d 0 1 2 (by decide) (by decide) (by decide)
  have c1 := across_cap S hc d 1 0 2 (by decide) (by decide) (by decide)
  have c2 := across_cap S hc d 2 0 1 (by decide) (by decide) (by decide)
  have cd := internal_cap S d 0 1 2 (by decide) (by decide) (by decide)
  have h0 := high 0
  have h1 := high 1
  have h2 := high 2
  omega

#print axioms impossible
end ThreeShores

/-- Every deletion of one vertex in a degree-four graph leaves at most
two components under the Graffiti.pc #189 parity bound. -/
theorem component_card_le_two_at_articulation (hc : G.Connected) (c : V)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v) :
    Nat.card (G.induce {v : V | v≠c}).ConnectedComponent≤2 := by
  classical
  let J := G.induce {v : V | v≠c}
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun t=>t.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent ≤ 2
  rw [Nat.card_eq_fintype_card]
  by_contra! many
  have h3 : 3 ≤ Fintype.card J.ConnectedComponent := by omega
  let C (i : Fin 3) := (Fintype.equivFin J.ConnectedComponent).symm (Fin.castLE h3 i)
  have inj : Function.Injective C := by
    intro i j eq
    have e := (Fintype.equivFin J.ConnectedComponent).symm.injective eq
    have q := congrArg (fun u : Fin (Fintype.card J.ConnectedComponent) => u.val) e
    exact Fin.ext q
  let H (i : Fin 3) : Finset V := univ.filter (fun x=>
    ∃ h : x≠c, J.connectedComponentMk ⟨x,h⟩=C i)
  have mem {i : Fin 3} {x : V} : x∈H i ↔ ∃ h : x≠c,J.connectedComponentMk ⟨x,h⟩=C i := by simp [H]
  have off (i : Fin 3) : c∉H i := fun h=>(mem.mp h).choose rfl
  have nonempty (i : Fin 3) : (H i).Nonempty := by
    obtain ⟨x,hx⟩ := (C i).exists_rep
    exact ⟨x.val,mem.mpr ⟨x.property,hx⟩⟩
  have closed (i : Fin 3) (x : V) (xi : x∈H i) (y : V) (xy : G.Adj x y) :
      y=c ∨ y∈H i := by
    by_cases yc : y=c
    · exact .inl yc
    obtain ⟨xc,xi⟩ := mem.mp xi
    have e : J.Adj ⟨x,xc⟩ ⟨y,yc⟩ := xy
    exact .inr (mem.mpr ⟨yc,(ConnectedComponent.sound e.reachable).symm.trans xi⟩)
  have joined (i : Fin 3) : (G.induce (↑(H i) : Set V)).Connected := by
    apply induced_connected_of_joined (H i) (nonempty i)
    intro x xi y yi
    obtain ⟨xc,ci⟩ := mem.mp xi
    obtain ⟨yc,di⟩ := mem.mp yi
    obtain ⟨w⟩ := ConnectedComponent.exact (ci.trans di.symm)
    let f : J →g G := {toFun := Subtype.val, map_rel' := fun e=>e}
    refine ⟨w.map f,?_⟩
    intro z hz
    rw [support_map,List.mem_map] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    have r := ConnectedComponent.sound (w.takeUntil v hv).reachable
    exact mem.mpr ⟨v.property,r.symm.trans ci⟩
  have hit (i : Fin 3) : ∃ x∈H i,G.Adj c x := by
    apply Classical.byContradiction
    intro no
    obtain ⟨v,vi⟩ := nonempty i
    obtain ⟨w⟩ := hc.preconnected v c
    have stay {x y : V} (p : G.Walk x y) : x∈H i → y∈H i := by
      induction p with
      | nil => exact id
      | @cons x z y xz p ih =>
        intro xi
        apply ih
        rcases closed i x xi z xz with e|h
        · exact (no ⟨x,xi,e ▸ xz.symm⟩).elim
        · exact h
    exact off i (stay w vi)
  have dis (i j : Fin 3) (ne : i≠j) : Disjoint (H i) (H j) := by
    apply disjoint_left.mpr
    intro x xi xj
    obtain ⟨h,hi⟩ := mem.mp xi
    obtain ⟨_,hj⟩ := mem.mp xj
    exact ne (inj (hi.symm.trans hj))
  exact (ThreeShores.mk H dis off closed joined hit).impossible hc even degree

#print axioms component_card_le_two_at_articulation
end Graffiti189LongestPath.CrossSaturation
