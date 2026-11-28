import SmallSeparator189
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.distance_on_geodesic from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 6500000
namespace Graffiti189LongestPath.StandaloneShellQuadratic
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Third-shell vertices reachable through a nonpin gateway of `u`. -/
noncomputable def gateThird (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (C : Finset V) (u : V) : Finset V := by
  classical
  exact (Shell G x 3).filter (fun z => ∃ b∈C,G.Adj u b ∧ G.Adj b z)

omit [DecidableEq V] in
theorem mem_gateThird {x u z : V} {C : Finset V} :
    z∈gateThird G x C u ↔ z∈Shell G x 3 ∧ ∃ b∈C,G.Adj u b ∧ G.Adj b z := by
  classical
  simp [gateThird]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A minimum donor set has a distinct private gate for each donor. -/
theorem exists_private_donor_cover (A C : Finset V)
    (initial : ∀ b∈C,∃ a∈A,G.Adj a b) :
    ∃ D⊆A, (∀ b∈C,∃ a∈D,G.Adj a b) ∧
      (∀ a∈D,∃ b∈C,G.Adj a b ∧ ∀ u∈D,u≠a → ¬G.Adj u b) := by
  classical
  let isCover (D : Finset V) : Prop := ∀ b∈C,∃ a∈D,G.Adj a b
  letI decCover : DecidablePred isCover := fun _ => Classical.propDecidable _
  let F := A.powerset.filter isCover
  have fm (D : Finset V) : D∈F ↔ D⊆A ∧ isCover D := by simp [F]
  have ne : F.Nonempty := ⟨A,(fm A).mpr ⟨Subset.rfl,initial⟩⟩
  obtain ⟨D,dm,mn⟩ := exists_min_image F Finset.card ne
  obtain ⟨DA,cover⟩ := (fm D).mp dm
  refine ⟨D,DA,cover,?_⟩
  intro a ad
  apply Classical.byContradiction
  intro no
  have cc (b : V) (bc : b∈C) : ∃ u∈D.erase a,G.Adj u b := by
    obtain ⟨u,ud,edge⟩ := cover b bc
    by_cases ua : u=a
    · subst u
      apply Classical.byContradiction
      intro fail
      apply no
      refine ⟨b,bc,edge,?_⟩
      intro u ud na ed
      exact fail ⟨u,mem_erase.mpr ⟨na,ud⟩,ed⟩
    · exact ⟨u,mem_erase.mpr ⟨ua,ud⟩,edge⟩
  have sm : D.erase a∈F := (fm _).mpr ⟨(erase_subset _ _).trans DA,cc⟩
  have h := mn (D.erase a) sm
  have c := card_erase_add_one ad
  omega

theorem universal_shell_three_quadratic (hc : G.Connected) (d : Nat)
    (cap : ∀ v,(DistanceTwo G v).card≤d)
    (x : V) :
    4*(Shell G x 3).card≤(d+1)*(d+1) := by
  classical
  let A := G.neighborFinset x
  let C := DistanceTwo G x
  let H := Shell G x 3
  let pay3 (u : V) := gateThird G x C u
  have getMid (z : V) (dz : G.dist x z=2) : ∃ u∈A,G.Adj u z := by
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
    have len := ql.trans dz
    let u := q.getVert 1
    have xu : G.Adj x u := by simpa [u] using q.adj_getVert_succ (i:=0) (by omega)
    have uz : G.Adj u z := by
      have e := q.adj_getVert_succ (i:=1) (by omega : 1<q.length)
      rwa [show q.getVert 2=z by rw [←len,getVert_length]] at e
    exact ⟨u,(G.mem_neighborFinset _ _).mpr xu,uz⟩
  have initial (v : V) (vc : v∈C) : ∃ u∈A,G.Adj u v :=
    getMid v (Graffiti189LongestPath.mem_distanceTwo.mp vc)
  have ck : C.card≤d := cap x
  obtain ⟨D,DA,DC,priv⟩ := exists_private_donor_cover A C initial
  have rep₀ (v : V) : ∃ b,v∈D → b∈C ∧ G.Adj v b ∧ ∀ u∈D,u≠v → ¬G.Adj u b := by
    by_cases vd : v∈D
    · obtain ⟨b,bc,e,safe⟩ := priv v vd
      exact ⟨b,fun _ => ⟨bc,e,safe⟩⟩
    · exact ⟨x,fun q => (vd q).elim⟩
  choose rep repP using rep₀
  have repInj : Set.InjOn rep (↑D : Set V) := by
    intro v vd w wd eq
    by_contra ne
    have e : G.Adj v (rep w) := eq ▸ (repP v vd).2.1
    exact (repP w wd).2.2 v vd ne e
  have rc : (D.image rep).card=D.card := card_image_of_injOn repInj
  have rsub : D.image rep⊆C := by
    intro z hz
    obtain ⟨v,vd,rfl⟩ := mem_image.mp hz
    exact (repP v vd).1
  have dm : D.card≤d := (rc ▸ card_le_card rsub).trans ck
  let HD := D.biUnion pay3
  have all : H⊆HD := by
    intro z hz
    have dz := mem_shell.mp hz
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
    have len := ql.trans dz
    let u := q.getVert 2
    have du : G.dist x u=2 := Graffiti189LongestPath.distance_on_geodesic hc q ql 2 (by omega)
    have uz : G.Adj u z := by
      have e := q.adj_getVert_succ (i:=2) (by omega : 2<q.length)
      rwa [show q.getVert 3=z by rw [←len,getVert_length]] at e
    have uc : u∈C := Graffiti189LongestPath.mem_distanceTwo.mpr du
    obtain ⟨w,wd,wu⟩ := DC u uc
    exact mem_biUnion.mpr ⟨w,wd,mem_gateThird.mpr ⟨hz,u,uc,wu,uz⟩⟩
  have near {u : V} (ua : u∈A) : G.dist x u=1 :=
    dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp ua)
  have noA {u : V} (uc : u∈C) : u∉A := by
    intro ua
    have h := near ua
    have g := Graffiti189LongestPath.mem_distanceTwo.mp uc
    omega
  have third_charge {u : V} (ua : u∈A) : pay3 u⊆DistanceTwo G u := by
    intro z zz
    obtain ⟨zs,b,_,ub,bz⟩ := mem_gateThird.mp zz
    have d₁ := near ua
    have d₃ := mem_shell.mp zs
    have ne : u≠z := by intro e; rw [e] at d₁; omega
    have no : ¬G.Adj u z := by
      intro e
      have d₂ := dist_eq_one_iff_adj.mpr e
      have tr := hc.dist_triangle (u:=x) (v:=u) (w:=z)
      omega
    exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne no ub bz)
  let m := D.card
  let bound := d+1
  have diet (v : V) (vd : v∈D) : (gateThird G x C v).card≤bound-m := by
    let E := D.erase v
    let pay (u : V) := if G.Adj v u then rep u else u
    let W := E.image pay
    have pinj : Set.InjOn pay (↑E : Set V) := by
      intro u uE w wE eq
      have ud := (mem_erase.mp uE).2
      have wd := (mem_erase.mp wE).2
      by_cases vu : G.Adj v u <;> by_cases vw : G.Adj v w
      · exact repInj ud wd (by simpa [pay,vu,vw] using eq)
      · have e : rep u=w := by simpa [pay,vu,vw] using eq
        exact (noA (repP u ud).1 (e.symm ▸ DA wd)).elim
      · have e : u=rep w := by simpa [pay,vu,vw] using eq
        exact (noA (repP w wd).1 (e ▸ DA ud)).elim
      · simpa [pay,vu,vw] using eq
    have wc : W.card=E.card := card_image_of_injOn pinj
    have ec : E.card+1=m := card_erase_add_one vd
    have spend : W⊆DistanceTwo G v := by
      intro z hz
      obtain ⟨u,ue,rfl⟩ := mem_image.mp hz
      obtain ⟨uv,ud⟩ := mem_erase.mp ue
      by_cases ad : G.Adj v u
      · have gp := repP u ud
        have no := gp.2.2 v vd uv.symm
        have ne : v≠rep u := fun e => noA gp.1 (e ▸ DA vd)
        have c := Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc ne no ad gp.2.1)
        simpa [pay,ad] using c
      · have vx := (G.mem_neighborFinset _ _).mp (DA vd)
        have ux := (G.mem_neighborFinset _ _).mp (DA ud)
        have c := Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc uv.symm ad vx.symm ux)
        simpa [pay,ad] using c
    have dis : Disjoint W (gateThird G x C v) := disjoint_left.mpr (by
      intro z zw zh
      obtain ⟨u,ue,rfl⟩ := mem_image.mp zw
      have ud := (mem_erase.mp ue).2
      have high := mem_shell.mp (mem_gateThird.mp zh).1
      by_cases e : G.Adj v u
      · have dt := Graffiti189LongestPath.mem_distanceTwo.mp (repP u ud).1
        simp only [pay,if_pos e] at high
        omega
      · have l := near (DA ud)
        simp only [pay,if_neg e] at high
        omega)
    have c := card_le_card (union_subset spend (third_charge (DA vd)))
    rw [card_union_of_disjoint dis] at c
    have cb := cap v
    dsimp only [bound]
    omega
  have HDc : HD.card≤m*(bound-m) := card_biUnion_le_card_mul D _ (bound-m) diet
  have a : H.card≤m*(bound-m) := (card_le_card all).trans HDc
  have mm : m≤bound := by dsimp [m,bound]; omega
  let rem := bound-m
  have eq : m+rem=bound := by dsimp [rem]; omega
  have quad : 4*(m*rem)≤bound*bound := by
    have q : 4*(m*rem)≤(m+rem)*(m+rem) := by
      have w : 4*((m:ℤ)*(rem:ℤ))≤((m:ℤ)+(rem:ℤ))*((m:ℤ)+(rem:ℤ)) := by
        nlinarith [sq_nonneg ((m:ℤ)-(rem:ℤ))]
      exact_mod_cast w
    rwa [eq] at q
  have a' := Nat.mul_le_mul_left 4 a
  change 4*H.card≤bound*bound
  exact a'.trans quad

#print axioms universal_shell_three_quadratic
end Graffiti189LongestPath.StandaloneShellQuadratic
