import P5CliqueOnePortAmbientBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem arm_take_length {U : Type*} {J : SimpleGraph U} {x y : U}
    (w : J.Walk x y) (i : Nat) : (w.take i).length=min i w.length := by
  induction w generalizing i with
  | nil => simp [SimpleGraph.Walk.take]
  | cons e w ih =>
    cases i with
    | zero => simp [SimpleGraph.Walk.take]
    | succ n =>
      simp [SimpleGraph.Walk.take,ih,←Nat.succ_min_succ]

private theorem arm_drop_length {U : Type*} {J : SimpleGraph U} {x y : U}
    (w : J.Walk x y) (i : Nat) : (w.drop i).length=w.length-i := by
  induction w generalizing i with
  | nil => simp [SimpleGraph.Walk.drop]
  | cons e w ih =>
    cases i with
    | zero => simp [SimpleGraph.Walk.drop]
    | succ n => simp [SimpleGraph.Walk.drop,ih]

private theorem arm_geodesic_rank {U : Type*} {J : SimpleGraph U} (hc : J.Connected) {x y : U}
    (w : J.Walk x y) (minw : w.length=J.dist x y) (i : Nat) (il : i≤w.length) :
    J.dist x (w.getVert i)=i := by
  have a := J.dist_le (w.take i)
  have b := J.dist_le (w.drop i)
  rw [arm_take_length,min_eq_left il] at a
  rw [arm_drop_length] at b
  have c := hc.dist_triangle (u:=x) (v:=w.getVert i) (w:=y)
  omega

private theorem exists_far_of_radius_four (r : 4≤radius G) (t : V) :
    ∃ w : V,4≤G.dist t w := by
  classical
  by_contra h
  have all (x : V) : G.dist t x≤3 := by
    by_contra bad
    exact h ⟨x,by omega⟩
  have rad : radius G≤3 := by
    unfold radius
    have hm : Finset.univ.sup (G.dist t)∈Finset.univ.image (fun u=>Finset.univ.sup (G.dist u)) :=
      Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩
    have hl := Finset.min_le hm
    cases e : (Finset.univ.image (fun u=>Finset.univ.sup (G.dist u))).min with
    | top => exact Nat.zero_le _
    | coe k =>
      have hu : k≤Finset.univ.sup (G.dist t) := by simpa [e] using hl
      exact hu.trans (Finset.sup_le_iff.mpr (fun x _=>all x))
  omega

theorem common_relay_radius_four_gives_core_arm
    (hc : G.Connected) (r : 4≤radius G) (D : Finset V)
    (Dconn : (G.induce (D : Set V)).Connected)
    (p : Fin 4→V) (pm : ∀ i,p i∈D) (t : V) (td : t∈D)
    (relay : ∀ i,G.Adj t (p i)) (attach : ∀ q∉D,∃ i,G.Adj q (p i)) :
    ∃ A : Fin 5→V,InducedPath G A ∧ (∀ j,A j∈D) ∧ A 0=t ∧
      (∀ i j,3≤j.val→¬G.Adj (p i) (A j)) := by
  classical
  obtain ⟨w,hw⟩ := exists_far_of_radius_four r t
  have wd : w∈D := by
    by_contra wo
    obtain ⟨i,qi⟩ := attach w wo
    have b := hc.dist_triangle (u:=t) (v:=p i) (w:=w)
    rw [dist_eq_one_iff_adj.mpr (relay i),dist_eq_one_iff_adj.mpr qi.symm] at b
    omega
  let J := G.induce (D : Set V)
  let x : (D : Set V) := ⟨t,td⟩
  let y : (D : Set V) := ⟨w,wd⟩
  obtain ⟨walk,ml⟩ := Dconn.exists_walk_length_eq_dist x y
  let inc : J →g G := ⟨Subtype.val,fun a=>a⟩
  have long : 4≤walk.length := hw.trans (by simpa [inc,x,y] using G.dist_le (walk.map inc))
  let B (i : Fin 5) := walk.getVert i.val
  let A (i : Fin 5) := (B i).val
  have rank (i : Fin 5) : J.dist x (B i)=i.val :=
    arm_geodesic_rank Dconn walk ml i.val (by omega)
  have induced : InducedPath G A := by
    refine ⟨fun i j eq=>Fin.ext (by rw [←rank i,←rank j,Subtype.ext eq]),?_⟩
    intro i j ij
    constructor
    · intro e
      have je : J.Adj (B i) (B j) := e
      have hh := Dconn.dist_triangle (u:=x) (v:=B i) (w:=B j)
      rw [rank,rank,dist_eq_one_iff_adj.mpr je] at hh
      have ii : i.val < j.val := ij
      omega
    · intro nat
      change J.Adj (walk.getVert i.val) (walk.getVert j.val)
      rw [←nat]
      exact walk.adj_getVert_succ (by omega)
  refine ⟨A,induced,fun j=>(B j).property,?_,?_⟩
  · exact congrArg Subtype.val (walk.getVert_zero)
  intro i j jl edge
  let pp : (D : Set V) := ⟨p i,pm i⟩
  have a : J.Adj x pp := relay i
  have b : J.Adj pp (B j) := edge
  have hh := Dconn.dist_triangle (u:=x) (v:=pp) (w:=B j)
  rw [rank,dist_eq_one_iff_adj.mpr a,dist_eq_one_iff_adj.mpr b] at hh
  omega

#print axioms common_relay_radius_four_gives_core_arm
end Graffiti133P5CliqueArms
