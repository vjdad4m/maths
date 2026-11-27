import P5CliqueOnePortAmbientBudget133
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem sparse_tree_take_length {U : Type*} {J : SimpleGraph U} {x y : U}
    (w : J.Walk x y) (i : Nat) : (w.take i).length=min i w.length := by
  induction w generalizing i with
  | nil => simp [SimpleGraph.Walk.take]
  | cons e w ih =>
    cases i with
    | zero => simp [SimpleGraph.Walk.take]
    | succ n =>
      simp [SimpleGraph.Walk.take,ih,←Nat.succ_min_succ]

private theorem sparse_tree_drop_length {U : Type*} {J : SimpleGraph U} {x y : U}
    (w : J.Walk x y) (i : Nat) : (w.drop i).length=w.length-i := by
  induction w generalizing i with
  | nil => simp [SimpleGraph.Walk.drop]
  | cons e w ih =>
    cases i with
    | zero => simp [SimpleGraph.Walk.drop]
    | succ n => simp [SimpleGraph.Walk.drop,ih]

private theorem sparse_tree_geodesic_rank {U : Type*} {J : SimpleGraph U} (hc : J.Connected) {x y : U}
    (w : J.Walk x y) (minw : w.length=J.dist x y) (i : Nat) (il : i≤w.length) :
    J.dist x (w.getVert i)=i := by
  have a := J.dist_le (w.take i)
  have b := J.dist_le (w.drop i)
  rw [sparse_tree_take_length,min_eq_left il] at a
  rw [sparse_tree_drop_length] at b
  have c := hc.dist_triangle (u:=x) (v:=w.getVert i) (w:=y)
  omega

private theorem sparse_tree_drop_getVert {U : Type*} {J : SimpleGraph U} {x y : U}
    (w : J.Walk x y) (i j : Nat) : (w.drop i).getVert j=w.getVert (i+j) := by
  induction w generalizing i with
  | nil => simp [SimpleGraph.Walk.drop]
  | cons e w ih =>
    cases i with
    | zero => simp [SimpleGraph.Walk.drop]
    | succ n => simp [SimpleGraph.Walk.drop,ih,Nat.succ_add]

private theorem sparse_tree_getVert_diff_bound {U : Type*} {J : SimpleGraph U} {x y : U}
    (w : J.Walk x y) (i j : Nat) (hij : i≤j) (hj : j≤w.length) :
    J.dist (w.getVert i) (w.getVert j)≤j-i := by
  have e : (w.drop i).getVert (j-i)=w.getVert j := by
    rw [sparse_tree_drop_getVert,Nat.add_sub_of_le hij]
  have h := J.dist_le ((w.drop i).take (j-i))
  rw [sparse_tree_take_length,sparse_tree_drop_length] at h
  have hh : min (j-i) (w.length-i)=j-i := min_eq_left (by omega)
  rwa [hh,e] at h

private theorem sparse_tree_unique_path_length {U : Type*} {J : SimpleGraph U}
    (tr : J.IsTree) {x y : U} (w : J.Walk x y) (wp : w.IsPath) :
    w.length = J.dist x y := by
  obtain ⟨a,ap,al⟩ := tr.1.exists_path_of_dist x y
  obtain ⟨q,qp,qu⟩ := tr.existsUnique_path x y
  have eq : w=a := (qu w wp).trans (qu a ap).symm
  rw [eq,al]

private theorem sparse_tree_append_isPath_of_only_intersect {U : Type*} {J : SimpleGraph U}
    {x z y : U} (u : J.Walk x z) (v : J.Walk z y)
    (up : u.IsPath) (vp : v.IsPath)
    (inter : ∀ w∈u.support,w∈v.support→w=z) : (u.append v).IsPath := by
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append]
  have hu := (Walk.isPath_def _).mp up
  have hv := (Walk.isPath_def _).mp vp
  rw [Walk.support_eq_cons,List.nodup_cons] at hv
  refine ⟨hu,hv.2,?_⟩
  intro a au av
  have az := inter a au (List.mem_of_mem_tail av)
  exact hv.1 (az ▸ av)

theorem sparse_tree_radius_two_of_diameter_le_four {U : Type*} [Fintype U] [DecidableEq U]
    {J : SimpleGraph U} (tr : J.IsTree) (small : ∀ x y,J.dist x y≤4) :
    ∃ c : U,∀ x,J.dist c x≤2 := by
  classical
  letI := tr.1.nonempty
  let F := (Finset.univ : Finset (U×U))
  obtain ⟨⟨a,b⟩,ab,diam⟩ := Finset.exists_mem_eq_sup F Finset.univ_nonempty
    (fun z=>J.dist z.1 z.2)
  have topD (x y : U) : J.dist x y≤J.dist a b := by
    rw [←diam]
    exact Finset.le_sup (f:=fun z=>J.dist z.1 z.2) (Finset.mem_univ (x,y))
  obtain ⟨P,pp,pL⟩ := tr.1.exists_path_of_dist a b
  let d := P.length
  let m := d/2
  have md : m≤d := Nat.div_le_self _ _
  let c := P.getVert m
  refine ⟨c,fun x=>?_⟩
  obtain ⟨W,wp,wl⟩ := tr.1.exists_path_of_dist x a
  have meet : {z∈P.support.toFinset | z∈W.support}.Nonempty :=
    ⟨a,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr P.start_mem_support,W.end_mem_support⟩⟩
  obtain ⟨z,zP,zW,first⟩ := W.exists_mem_support_forall_mem_support_imp_eq P.support.toFinset meet
  have zp : z∈P.support := List.mem_toFinset.mp zP
  let u := W.takeUntil z zW
  let v1 := (P.takeUntil z zp).reverse
  let v2 := P.dropUntil z zp
  have up : u.IsPath := wp.takeUntil zW
  have v1p : v1.IsPath := (pp.takeUntil zp).reverse
  have v2p : v2.IsPath := pp.dropUntil zp
  have v1sub : v1.support⊆P.support := by
    intro t tm
    exact P.support_takeUntil_subset zp (by simpa [v1,Walk.support_reverse] using tm)
  have v2sub : v2.support⊆P.support := P.support_dropUntil_subset zp
  have p1 : (u.append v1).IsPath := sparse_tree_append_isPath_of_only_intersect u v1 up v1p
    (fun t tu tv=>first t (List.mem_toFinset.mpr (v1sub tv)) tu)
  have p2 : (u.append v2).IsPath := sparse_tree_append_isPath_of_only_intersect u v2 up v2p
    (fun t tu tv=>first t (List.mem_toFinset.mpr (v2sub tv)) tu)
  have l1 := sparse_tree_unique_path_length tr _ p1
  have l2 := sparse_tree_unique_path_length tr _ p2
  rw [Walk.length_append] at l1 l2
  have da := topD x a
  have db := topD x b
  have sn := small a b
  obtain ⟨j,zj,jl⟩ := Walk.mem_support_iff_exists_getVert.mp zp
  have rank := sparse_tree_geodesic_rank tr.1 P pL j jl
  have v1len : v1.length=j := by
    have q := sparse_tree_unique_path_length tr (P.takeUntil z zp) (pp.takeUntil zp)
    change (P.takeUntil z zp).reverse.length=j
    rw [Walk.length_reverse]
    exact q.trans ((congrArg (J.dist a) zj).symm.trans rank)
  have v2len : v2.length+j=d := by
    have total := congrArg Walk.length (P.take_spec zp)
    rw [Walk.length_append] at total
    change (P.takeUntil z zp).length+v2.length=d at total
    have el : (P.takeUntil z zp).length=j := by simpa [v1] using v1len
    omega
  have ac : J.dist x z≤u.length := J.dist_le u
  have tri := tr.1.dist_triangle (u:=c) (v:=z) (w:=x)
  rw [dist_comm (G:=J) (u:=z) (v:=x)] at tri
  change P.getVert j=z at zj
  have sn' : d≤4 := pL.le.trans sn
  have pd : d=J.dist a b := pL
  by_cases mj : m≤j
  · have close := sparse_tree_getVert_diff_bound P m j mj jl
    change J.dist c (P.getVert j)≤j-m at close
    rw [zj] at close
    have hm : m=d/2 := rfl
    omega
  · have jm : j≤m := by omega
    have close := sparse_tree_getVert_diff_bound P j m jm md
    change J.dist (P.getVert j) c≤m-j at close
    rw [zj,dist_comm (G:=J) (u:=z) (v:=c)] at close
    have hm : m=d/2 := rfl
    omega

#print axioms sparse_tree_radius_two_of_diameter_le_four
/-- The first `k` steps of a shortest walk form a fully induced path. -/
theorem sparse_core_geodesic_prefix {U : Type*} {J : SimpleGraph U}
    (hc : J.Connected) {x y : U} (w : J.Walk x y) (short : w.length=J.dist x y)
    (k : Nat) (bound : k≤w.length+1) :
    InducedPath J (fun i : Fin k=>w.getVert i.val) := by
  have rank (i : Fin k) : J.dist x (w.getVert i.val)=i.val :=
    sparse_tree_geodesic_rank hc w short i.val (by omega)
  refine ⟨fun i j e=>Fin.ext ((rank i).symm.trans ((congrArg (J.dist x) e).trans (rank j))),?_⟩
  intro i j ij
  constructor
  · intro edge
    have h := hc.dist_triangle (u:=x) (v:=w.getVert i.val) (w:=w.getVert j.val)
    rw [rank,rank,dist_eq_one_iff_adj.mpr edge] at h
    have ij' : i.val < j.val := ij
    omega
  · intro eq
    change J.Adj (w.getVert i.val) (w.getVert j.val)
    rw [←eq]
    exact w.adj_getVert_succ (by omega)

def SparseLeaf {U : Type*} (J : SimpleGraph U) (x : U) : Prop :=
  ∀ y z, J.Adj x y→J.Adj x z→y=z

theorem sparse_tree_endpoint_leaf_of_diametral_walk {U : Type*} {J : SimpleGraph U}
    (tr : J.IsTree) {x y : U} (w : J.Walk x y) (short : w.length=J.dist x y)
    (diam : ∀ a b,J.dist a b≤w.length) : SparseLeaf J x := by
  have only (u : U) (xu : J.Adj x u) : u=w.getVert 1 := by
    by_cases um : u∈w.support
    · obtain ⟨j,jm,jl⟩ := Walk.mem_support_iff_exists_getVert.mp um
      have r := sparse_tree_geodesic_rank tr.1 w short j jl
      rw [jm,dist_eq_one_iff_adj.mpr xu] at r
      rw [←r] at jm
      exact jm.symm
    · let z := w.cons xu.symm
      have zp : z.IsPath := (w.isPath_of_length_eq_dist short).cons um
      have eq := sparse_tree_unique_path_length tr z zp
      have le := diam u y
      change w.length+1=J.dist u y at eq
      omega
  exact fun a b ha hb=>(only a ha).trans (only b hb).symm

theorem sparse_tree_diameter_five_arm_from_ambient_radius
    (conn : G.Connected) (rad : 4≤radius G) (D : Finset V)
    (dom : ∀ x∉D,∃ y∈D,G.Adj x y)
    (tr : (G.induce (D : Set V)).IsTree) (h7 : NoPath (G.induce (D : Set V)) 7) :
    ∃ f : Fin 6→(D : Set V), InducedPath (G.induce (D : Set V)) f ∧
      SparseLeaf (G.induce (D : Set V)) (f 0) ∧ SparseLeaf (G.induce (D : Set V)) (f 5) := by
  classical
  let J := G.induce (D : Set V)
  let inc : J →g G := ⟨Subtype.val,fun e=>e⟩
  have max5 (x y : (D : Set V)) : J.dist x y≤5 := by
    by_cases le : J.dist x y≤5
    · exact le
    exfalso
    obtain ⟨w,h⟩ := tr.1.exists_walk_length_eq_dist x y
    change w.length=J.dist x y at h
    exact h7 ⟨_,sparse_core_geodesic_prefix tr.1 w h 7 (by omega)⟩
  have far : ∃ x y : (D : Set V),J.dist x y=5 := by
    by_contra! no
    have small (x y : (D : Set V)) : J.dist x y≤4 := by
      have h := max5 x y
      exact Nat.le_of_lt_succ (lt_of_le_of_ne h (no x y))
    obtain ⟨q,hq⟩ := sparse_tree_radius_two_of_diameter_le_four tr small
    have in2 (x : (D : Set V)) : G.dist q.val x.val≤2 := by
      obtain ⟨w,wl⟩ := tr.1.exists_walk_length_eq_dist q x
      have b : G.dist q.val x.val≤w.length := by simpa [inc] using G.dist_le (w.map inc)
      exact b.trans (wl.le.trans (hq x))
    have all (x : V) : G.dist q.val x≤3 := by
      by_cases xd : x∈D
      · exact (in2 ⟨x,xd⟩).trans (by decide)
      obtain ⟨y,ym,xy⟩ := dom x xd
      have h := conn.dist_triangle (u:=q.val) (v:=y) (w:=x)
      rw [dist_eq_one_iff_adj.mpr xy.symm] at h
      have b := in2 ⟨y,ym⟩
      change G.dist q.val y≤2 at b
      omega
    have rz : radius G≤3 := by
      unfold radius
      have hm : Finset.univ.sup (G.dist q.val)∈Finset.univ.image (fun u=>Finset.univ.sup (G.dist u)) :=
        Finset.mem_image.mpr ⟨q.val,Finset.mem_univ _,rfl⟩
      have hl := Finset.min_le hm
      cases e : (Finset.univ.image (fun u=>Finset.univ.sup (G.dist u))).min with
      | top => exact Nat.zero_le _
      | coe k =>
        have hu : k≤Finset.univ.sup (G.dist q.val) := by simpa [e] using hl
        exact hu.trans (Finset.sup_le_iff.mpr (fun x _=>all x))
    omega
  obtain ⟨x,y,xy⟩ := far
  obtain ⟨w,wl⟩ := tr.1.exists_walk_length_eq_dist x y
  change w.length=J.dist x y at wl
  have len := wl.trans xy
  let f (i : Fin 6) := w.getVert i.val
  have e0 : f 0=x := w.getVert_zero
  have e5 : f 5=y := by
    change w.getVert 5=y
    rw [←len]
    exact w.getVert_length
  have lf : SparseLeaf J x :=
    sparse_tree_endpoint_leaf_of_diametral_walk tr w wl (fun a b=>(max5 a b).trans len.ge)
  have wr : w.reverse.length=J.dist y x := by
    rw [Walk.length_reverse,wl,dist_comm]
  have rf : SparseLeaf J y :=
    sparse_tree_endpoint_leaf_of_diametral_walk tr w.reverse wr (fun a b=>by
      rw [Walk.length_reverse,len]
      exact max5 a b)
  exact ⟨f,sparse_core_geodesic_prefix tr.1 w wl 6 (by omega),e0.symm ▸ lf,e5.symm ▸ rf⟩

#print axioms sparse_core_geodesic_prefix
#print axioms sparse_tree_endpoint_leaf_of_diametral_walk
#print axioms sparse_tree_diameter_five_arm_from_ambient_radius
end Graffiti133P5CliqueArms
