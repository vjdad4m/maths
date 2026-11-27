import NestedCoreLongGateAtlas133
import NestedCoreShortCrossingScore133
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti133NestedLongGates
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
  Graffiti133CoreSeven Graffiti133NestedSingleGate Graffiti133MultiWeighted
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem separate_matches (H : Hole G 7) (h4 : FourCycleFree G)
    {x y : V} {p q : Fin 14} (ne : x≠y) (px : Matches H x p) (qy : Matches H y q) :
    Separate p q := by
  classical
  unfold Separate
  apply Finset.card_le_one.mpr
  intro a am b bm
  obtain ⟨ap,aq⟩ := Finset.mem_inter.mp am
  obtain ⟨bp,bq⟩ := Finset.mem_inter.mp bm
  exact H.inj (h4 x y (H.c a) (H.c b) ne ((px a).mpr ap) ((qy a).mpr aq)
    ((px b).mpr bp) ((qy b).mpr bq))

private theorem distinct_matches (H : Hole G 7) (h4 : FourCycleFree G)
    {x y : V} {p q : Fin 14} (ne : x≠y) (px : Matches H x p) (qy : Matches H y q) : p≠q := by
  intro e
  subst q
  have h := separate_matches H h4 ne px qy
  unfold Separate at h
  rw [Finset.inter_self] at h
  have h2 := profile_at_least_two p
  omega

theorem match_long_gate (H : Hole G 7) (h4 : FourCycleFree G)
    (x : V) (off : Outside H.c x) (hit : (contactSet H x).Nonempty)
    (long : ¬VeryShortGate H x) : ∃ p,Matches H x p := by
  rcases allowed_nonempty_profile_type _ (contacts_are_allowed H h4 x off) hit with short|short|ok
  · obtain ⟨i,one⟩ := short
    apply False.elim
    apply long
    refine ⟨off,i,Or.inl ?_⟩
    intro k
    rw [←mem_contactSet H x k,one,Finset.mem_singleton]
  · obtain ⟨i,two⟩ := short
    apply False.elim
    apply long
    refine ⟨off,i,Or.inr ?_⟩
    intro k
    rw [←mem_contactSet H x k,two,Finset.mem_insert,Finset.mem_singleton]
  · obtain ⟨i,eq⟩ := ok
    exact ⟨i,fun k=>(mem_contactSet H x k).symm.trans (by rw [eq])⟩

private theorem two_step_bound (hc : G.Connected) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c≤2 := by
  have t : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
  rwa [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at t

private theorem radius_upper_of_center (a : V) (n : Nat) (bound : ∀ x,G.dist a x≤n) :
    radius G≤n := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist a) ∈ Finset.univ.image (fun v=>Finset.univ.sup (G.dist v)) :=
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u=>Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d≤Finset.univ.sup (G.dist a) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _=>bound w))

theorem radius_three_of_four_long_gates
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (K : Finset V) (cy : ∀ i,H.c i∈K)
    (dom : ∀ x : V,x∈K ∨ ∃ y∈K,G.Adj x y)
    (h7 : ¬∃ f : Fin 7→(K : Set V),InducedPath (G.induce (K : Set V)) f)
    (u v x y : V) (um : u∈K) (vm : v∈K)
    (sizeK : ∀ w∈K,(∃ i,H.c i=w) ∨ w=u ∨ w=v)
    (uo : Outside H.c u) (vo : Outside H.c v) (xo : Outside H.c x) (yo : Outside H.c y)
    (uv : u≠v) (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y) (xy : x≠y)
    (uh : (contactSet H u).Nonempty) (vh : (contactSet H v).Nonempty)
    (xh : (contactSet H x).Nonempty) (yh : (contactSet H y).Nonempty)
    (xlong : ¬VeryShortGate H x) (ylong : ¬VeryShortGate H y) : radius G≤3 := by
  let J := G.induce (K : Set V)
  let HJ := restrictedHole H K cy
  let U : (K : Set V) := ⟨u,um⟩
  let W : (K : Set V) := ⟨v,vm⟩
  have Uoff : Outside HJ.c U := fun i e=>uo i (congrArg Subtype.val e)
  have Woff : Outside HJ.c W := fun i e=>vo i (congrArg Subtype.val e)
  have Uhit : ∃ i,J.Adj U (HJ.c i) := by
    obtain ⟨i,im⟩ := uh
    exact ⟨i,(mem_contactSet H u i).mp im⟩
  have Whit : ∃ i,J.Adj W (HJ.c i) := by
    obtain ⟨i,im⟩ := vh
    exact ⟨i,(mem_contactSet H v i).mp im⟩
  obtain ⟨p,up⟩ := classify_profile HJ (restricted_c4 h4 K) h7 U Uoff Uhit
  obtain ⟨q,vq⟩ := classify_profile HJ (restricted_c4 h4 K) h7 W Woff Whit
  obtain ⟨r,xr⟩ := match_long_gate H h4 x xo xh xlong
  obtain ⟨s,ys⟩ := match_long_gate H h4 y yo yh ylong
  have pu : Matches H u p := up
  have qv : Matches H v q := vq
  have pq := distinct_matches H h4 uv pu qv
  have ok := (classify_pair HJ (restricted_c4 h4 K) h7 Uoff Woff
    (fun e=>uv (congrArg Subtype.val e)) pq up vq).1
  obtain ⟨i,far,uc,vc⟩ := four_long_gate_profile_center p q r s ok
    (separate_matches H h4 uv pu qv) (separate_matches H h4 ux pu xr)
    (separate_matches H h4 uy pu ys) (separate_matches H h4 vx qv xr)
    (separate_matches H h4 vy qv ys) (separate_matches H h4 xy xr ys)
  have cycle (j : Fin 7) : G.dist (H.c i) (H.c j)≤2 := by
    by_cases eq : i=j
    · rw [←eq,dist_self]
      decide
    by_cases near : Cyclic i j
    · rw [dist_eq_one_iff_adj.mpr ((H.adj i j).mpr near)]
      decide
    by_cases mid : ∃ k,Cyclic i k ∧ Cyclic j k
    · obtain ⟨k,ik,jk⟩ := mid
      exact two_step_bound hc ((H.adj i k).mpr ik) ((H.adj j k).mpr jk).symm
    · rcases far j ⟨eq,near,mid⟩ with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
      · exact two_step_bound hc ((pu i).mpr a).symm ((pu j).mpr b)
      · exact two_step_bound hc ((qv i).mpr a).symm ((qv j).mpr b)
      · exact two_step_bound hc ((xr i).mpr a).symm ((xr j).mpr b)
      · exact two_step_bound hc ((ys i).mpr a).symm ((ys j).mpr b)
  have toGate {z : V} {t : Fin 14} (m : Matches H z t)
      (hit : ∃ j : Fin 7,j∈profileContacts t ∧ (j=i ∨ Cyclic i j)) :
      G.dist (H.c i) z≤2 := by
    obtain ⟨j,jm,eq|adj⟩ := hit
    · subst j
      rw [dist_eq_one_iff_adj.mpr ((m i).mpr jm).symm]
      decide
    · exact two_step_bound hc ((H.adj i j).mpr adj) ((m j).mpr jm).symm
  have toCore (w : V) (wm : w∈K) : G.dist (H.c i) w≤2 := by
    rcases sizeK w wm with ⟨j,rfl⟩|rfl|rfl
    · exact cycle j
    · exact toGate pu uc
    · exact toGate qv vc
  apply radius_upper_of_center (H.c i) 3
  intro w
  rcases dom w with hm|⟨k,km,wk⟩
  · exact (toCore w hm).trans (by decide)
  · have td : G.dist (H.c i) w≤G.dist (H.c i) k+G.dist k w := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr wk.symm] at td
    have := toCore k km
    omega

#print axioms match_long_gate
#print axioms radius_three_of_four_long_gates
end Graffiti133NestedLongGates
