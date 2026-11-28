import AdjacentCutFiveMetric189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_nonempty shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Vis vis_sub vis_card_ge_two degree_le_shore_add_one positive_cap sum_subset_card count_sum
  from AdjacentCutFiveComponents189
open private mem_positive from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem singleton_dist_succ_depth (hc : G.Connected)
    (D : (CutGraph (G := G) a b).ConnectedComponent) {x y : V}
    (one : Shore D = {x}) (ax : G.Adj a x) (bx : G.Adj b x) (yx : y ≠ x) :
    G.dist x y = depth G a b y + 1 := by
  have inD : x∈Shore D := by simp [one]
  have out : y∉Shore D := by simpa [one] using yx
  rw [cross_metric (Shore D) hc inD out (shore_closed D),
    dist_eq_one_iff_adj.mpr ax.symm,dist_eq_one_iff_adj.mpr bx.symm]
  unfold depth
  omega

theorem depth_eq_one_of_port (hc : G.Connected) {z : V} (za : z≠a) (zb : z≠b)
    (vis : G.Adj a z ∨ G.Adj b z) : depth G a b z = 1 := by
  have aa := hc.pos_dist_of_ne (u:=a) (v:=z) za.symm
  have bb := hc.pos_dist_of_ne (u:=b) (v:=z) zb.symm
  unfold depth
  rcases vis with e|e
  · rw [dist_eq_one_iff_adj.mpr e]; omega
  · rw [dist_eq_one_iff_adj.mpr e]; omega

theorem at_most_one_depth_three_of_three_and_singleton (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3)
    (D : (CutGraph (G := G) a b).ConnectedComponent) (singleton : (Shore D).card = 1) :
    ∀ u v : V, depth G a b u = 3 → depth G a b v = 3 → u = v := by
  classical
  let J := CutGraph (G := G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent = 3 at three
  rw [Nat.card_eq_fintype_card] at three
  let T : Finset J.ConnectedComponent := univ.erase D
  have t2 : T.card = 2 := by simp [T, three]
  obtain ⟨x,dx⟩ := card_eq_one.mp singleton
  obtain ⟨xa,ha,ax⟩ := shore_hit_a ab conn D
  obtain ⟨xb,hb,bx⟩ := shore_hit_b ab conn D
  rw [dx,mem_singleton] at ha hb
  subst xa
  subst xb
  have xc : x∈Shore D := by simp [dx]
  have depthx := depth_eq_one_of_port (a:=a) (b:=b) hc
    (fun e => (shore_off D).1 (by simpa only [e] using xc)) (fun e => (shore_off D).2 (by simpa only [e] using xc)) (.inl ax)
  have xlo : G.degree x < 5 := by
    have q := degree_le_shore_add_one D xc
    omega
  have port_sub (C : J.ConnectedComponent) (ct : C∈T) : Vis C ⊆ PositiveEven G x := by
    intro z hz
    have hz' := mem_filter.mp hz
    have dc := (mem_erase.mp ct).1.symm
    rw [mem_positive]
    have zx : z ≠ x := fun e => disjoint_left.mp (shore_disjoint dc) xc (by simpa only [e] using hz'.1)
    have d := depth_eq_one_of_port (a:=a) (b:=b) hc
      (fun e => (shore_off C).1 (by simpa only [e] using hz'.1)) (fun e => (shore_off C).2 (by simpa only [e] using hz'.1)) hz'.2
    exact ⟨zx, by rw [singleton_dist_succ_depth hc D dx ax bx zx,d]; decide⟩
  have vis2 (C : J.ConnectedComponent) (ct : C ∈ T) : 2 ≤ (Vis C).card := by
    obtain ⟨z,zc⟩ := shore_nonempty C
    have nz : x ≠ z := fun h => disjoint_left.mp
      (shore_disjoint (mem_erase.mp ct).1.symm) xc (by simpa only [← h] using zc)
    have high := (degree x z nz).resolve_left (by omega)
    have le := degree_le_shore_add_one C zc
    exact vis_card_ge_two ab conn C (by omega)
  intro u v u3 v3
  by_contra uv
  have uP : u ∈ PositiveEven G x := by
    have ux : u ≠ x := by intro e; rw [e,depthx] at u3; contradiction
    exact mem_positive.mpr ⟨ux,by rw [singleton_dist_succ_depth hc D dx ax bx ux,u3]; decide⟩
  have vP : v ∈ PositiveEven G x := by
    have vx : v ≠ x := by intro e; rw [e,depthx] at v3; contradiction
    exact mem_positive.mpr ⟨vx,by rw [singleton_dist_succ_depth hc D dx ax bx vx,v3]; decide⟩
  let P := (PositiveEven G x).erase u |>.erase v
  have fits (C : J.ConnectedComponent) (ct : C∈T) : Vis C ⊆ P := by
    intro z hz
    have hz' := mem_filter.mp hz
    have dep := depth_eq_one_of_port (a:=a) (b:=b) hc
      (fun e => (shore_off C).1 (by simpa only [e] using hz'.1)) (fun e => (shore_off C).2 (by simpa only [e] using hz'.1)) hz'.2
    have zu : z ≠ u := by intro e; rw [e,u3] at dep; contradiction
    have zv : z ≠ v := by intro e; rw [e,v3] at dep; contradiction
    exact mem_erase.mpr ⟨zv,mem_erase.mpr ⟨zu,port_sub C ct hz⟩⟩
  have upper : (∑ C∈T,(Vis C).card) ≤ P.card := sum_subset_card T Vis (fun C _=>vis_sub C) P fits
  have lower : T.card * 2 ≤ ∑ C∈T,(Vis C).card := count_sum T Vis 2 vis2
  have p1 := card_erase_add_one uP
  have p2 : P.card + 1 = ((PositiveEven G x).erase u).card :=
    card_erase_add_one (mem_erase.mpr ⟨Ne.symm uv,vP⟩)
  have cap := positive_cap x even
  omega

theorem depth_le_three_of_three_and_singleton (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3)
    (D : (CutGraph (G := G) a b).ConnectedComponent) (singleton : (Shore D).card = 1) :
    ∀ z : V, depth G a b z ≤ 3 := by
  intro z
  by_contra! h
  obtain ⟨u,v,uv,du,dv⟩ := two_vertices_in_intermediate_depth hc conn (by decide : 0<3) h
  exact uv (at_most_one_depth_three_of_three_and_singleton hc ab even conn degree three D singleton u v du dv)

#print axioms at_most_one_depth_three_of_three_and_singleton
#print axioms depth_le_three_of_three_and_singleton
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
