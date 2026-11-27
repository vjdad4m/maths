import P5CliqueSmallCoreLocal133
import P5CliqueMultiPortBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

private theorem uniform_degree_sum {k : Nat} (h : ∀ v,G.degree v=k) :
    2*G.edgeFinset.card=k*Fintype.card V := by
  rw [←G.sum_degrees_eq_twice_card_edges]
  simp [h,Nat.mul_comm]

private theorem sum_at_most_except_one (d : V→Nat) (k l : Nat) (x : V)
    (low : d x≤l) (all : ∀ y≠x,d y≤k) :
    (∑ y : V,d y)≤ l+k*(Fintype.card V-1) := by
  classical
  let T := (Finset.univ : Finset V).erase x
  have cap : (∑ y∈T,d y)≤k*(Fintype.card V-1) := by
    calc
      _≤∑ _y∈T,k := Finset.sum_le_sum (fun y ym=>all y (Finset.mem_erase.mp ym).1)
      _=_ := by simp [T,Nat.mul_comm,Finset.card_erase_of_mem]
  have s := Finset.sum_erase_add (Finset.univ : Finset V) d (Finset.mem_univ x)
  change (∑ y∈T,d y)+d x=(∑ y : V,d y) at s
  omega

private theorem triangle_gives_three_low_scores (k : Nat)
    (cap : ∀ v,G.degree v≤k) (v a b : V)
    (va : G.Adj v a) (vb : G.Adj v b) (ab : G.Adj a b) :
    (∑ x : V,localIndependence G x)≤3*(k-1)+k*(Fintype.card V-3) := by
  classical
  let S : Finset V := {v,a,b}
  let T := (Finset.univ : Finset V)\S
  have sc : S.card=3 := by simp [S,va.ne,vb.ne,ab.ne]
  have sB : (∑ x∈S,localIndependence G x)≤3*(k-1) := by
    calc
      _≤∑ _x∈S,(k-1) := by
        apply Finset.sum_le_sum
        intro x xm
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at xm
        rcases xm with e|e|e
        · have q := small_local_triangle_loss v a b va vb ab
          have c := cap v
          rw [e]
          omega
        · have q := small_local_triangle_loss a v b va.symm ab vb
          have c := cap a
          rw [e]
          omega
        · have q := small_local_triangle_loss b a v ab.symm vb.symm va.symm
          have c := cap b
          rw [e]
          omega
      _=_ := by simp [sc]
  have tc : T.card=Fintype.card V-3 := by
    have co := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ,sc] at co
    change T.card+3=Fintype.card V at co
    omega
  have tB : (∑ x∈T,localIndependence G x)≤k*(Fintype.card V-3) := by
    calc
      _≤∑ _x∈T,k := Finset.sum_le_sum (fun x _=>(small_local_le_degree x).trans (cap x))
      _=_ := by simp [tc,Nat.mul_comm]
  have eq := Finset.sum_sdiff (Finset.subset_univ S) (f:=localIndependence G)
  change (∑ x∈T,localIndependence G x)+(∑ x∈S,localIndependence G x)=(∑ x : V,localIndependence G x) at eq
  omega

private theorem small_core_four_base (h4 : FourCycleFree G) (n4 : Fintype.card V=4) :
    (∑ x : V,localIndependence G x)≤6 := by
  classical
  have dmax (v : V) : G.degree v≤3 := by
    have le := Finset.card_le_card (show G.neighborFinset v⊆Finset.univ.erase v from by
      intro x xm
      exact Finset.mem_erase.mpr ⟨(small_mem_neighbor.mp xm).ne.symm,Finset.mem_univ _⟩)
    rw [G.card_neighborFinset_eq_degree,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,n4] at le
    exact le
  by_cases dg : ∃ v,G.degree v=3
  · obtain ⟨v,dv⟩ := dg
    have sub : G.neighborFinset v⊆Finset.univ.erase v := by
      intro x xm
      exact Finset.mem_erase.mpr ⟨(small_mem_neighbor.mp xm).ne.symm,Finset.mem_univ _⟩
    have eq : G.neighborFinset v=Finset.univ.erase v := by
      apply Finset.eq_of_subset_of_card_le sub
      rw [G.card_neighborFinset_eq_degree,dv,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,n4]
    have universal (x : V) (xv : x≠v) : G.Adj v x :=
      small_mem_neighbor.mp (eq.symm ▸ Finset.mem_erase.mpr ⟨xv,Finset.mem_univ _⟩)
    have lo (x : V) (xv : x≠v) : localIndependence G x≤1 := by
      unfold localIndependence
      apply Finset.sup_le_iff.mpr
      intro S sm
      have adj : (∀ a∈S,G.Adj x a) ∧ (∀ a∈S,∀ b∈S,¬G.Adj a b) := by
        simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
          Finset.mem_univ,true_and] using sm
      apply Finset.card_le_one.mpr
      intro a am b bm
      by_cases av : a=v
      · by_cases bv : b=v
        · exact av.trans bv.symm
        exact ((adj.2 a am b bm) (av.symm ▸ universal b bv)).elim
      by_cases bv : b=v
      · exact ((adj.2 b bm a am) (bv.symm ▸ universal a av)).elim
      exact h4 v x a b xv.symm (universal a av) (adj.1 a am) (universal b bv) (adj.1 b bm)
    have bound := sum_at_most_except_one (localIndependence G) 1 3 v
      ((small_local_le_degree v).trans (dmax v)) lo
    omega
  have d2 (v : V) : G.degree v≤2 := by
    have le := dmax v
    have ne : G.degree v≠3 := fun e=>dg ⟨v,e⟩
    omega
  by_cases steady : ∀ v,G.degree v=2
  · have existT : ∃ v a b,G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
      by_contra! free
      have pos : 0<Fintype.card V := by omega
      let v : V := Classical.choice (Fintype.card_pos_iff.mp pos)
      have tw := smallTwoHop_lower_degree h4 1 (fun x=>by simp [steady]) v
      have b := smallTwoHop_trianglefree_bound v (free v)
      rw [steady] at tw b
      omega
    obtain ⟨v,a,b,va,vb,ab⟩ := existT
    have le := triangle_gives_three_low_scores 2 d2 v a b va vb ab
    omega
  push_neg at steady
  obtain ⟨v,hv⟩ := steady
  have l1 : G.degree v≤1 := by have h := d2 v; omega
  have s := sum_at_most_except_one (fun x=>G.degree x) 2 1 v l1 (fun y _=>d2 y)
  change (∑ x : V,G.degree x)≤1+2*(Fintype.card V-1) at s
  have sum := G.sum_degrees_eq_twice_card_edges
  have dom : (∑ v : V,localIndependence G v)≤∑ v : V,G.degree v :=
    Finset.sum_le_sum (fun v _=>small_local_le_degree v)
  omega

private theorem small_core_min_three_case (h4 : FourCycleFree G)
    (h4n : 4≤Fintype.card V) (n9 : Fintype.card V≤9)
    (dmin : ∀ v,3≤G.degree v) :
    (∑ v : V,localIndependence G v)+10≤4*Fintype.card V := by
  classical
  let n := Fintype.card V
  have hi (v : V) : 2*G.degree v≤n-1 := by
    have cap := Finset.card_le_card (smallTwoHop_sub (G:=G) v)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ] at cap
    exact (smallTwoHop_lower_degree h4 2 dmin v).trans cap
  have ne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := ne
  have nge : 7≤n := by
    have p := hi a
    have q := dmin a
    omega
  by_cases n7 : n=7
  · have all (v : V) : G.degree v=3 := by
      have a := hi v
      have b := dmin v
      omega
    have p := uniform_degree_sum all
    omega
  by_cases n8 : n=8
  · have all (v : V) : G.degree v=3 := by
      have a := hi v
      have b := dmin v
      omega
    have existT : ∃ v a b,G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
      by_contra! free
      have lc := smallTwoHop_lower_degree h4 2 dmin a
      have uc := smallTwoHop_trianglefree_bound a (free a)
      rw [all] at lc uc
      omega
    obtain ⟨v,x,y,vx,vy,xy⟩ := existT
    have loss := triangle_gives_three_low_scores 3 (fun v=>(all v).le) v x y vx vy xy
    omega
  have nn : n=9 := by omega
  have all (v : V) : G.degree v=3 ∨ G.degree v=4 := by
    have a := hi v
    have b := dmin v
    omega
  have cap (v : V) : localIndependence G v≤3 := by
    rcases all v with d|d
    · exact (small_local_le_degree v).trans d.le
    · have full : smallTwoHop G v=Finset.univ.erase v := by
        apply Finset.eq_of_subset_of_card_le (smallTwoHop_sub v)
        have a := smallTwoHop_lower_degree h4 2 dmin v
        rw [d] at a
        rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
        omega
      have fullN : G.neighborFinset v⊆smallTwoHop G v := by
        rw [full]
        intro x xm
        exact Finset.mem_erase.mpr ⟨(small_mem_neighbor.mp xm).ne.symm,Finset.mem_univ _⟩
      have qq := small_local_perfect_matching_bound h4 v fullN
      omega
  have there : ∃ v,G.degree v=4 := by
    by_contra! no
    have all3 (v : V) : G.degree v=3 := (all v).resolve_right (no v)
    have odd := uniform_degree_sum all3
    omega
  obtain ⟨b,db⟩ := there
  have two : localIndependence G b≤2 := by
    have full : smallTwoHop G b=Finset.univ.erase b := by
      apply Finset.eq_of_subset_of_card_le (smallTwoHop_sub b)
      have a := smallTwoHop_lower_degree h4 2 dmin b
      rw [db] at a
      rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
      omega
    have fullN : G.neighborFinset b⊆smallTwoHop G b := by
      rw [full]
      intro x xm
      exact Finset.mem_erase.mpr ⟨(small_mem_neighbor.mp xm).ne.symm,Finset.mem_univ _⟩
    have qq := small_local_perfect_matching_bound h4 b fullN
    omega
  have ss := sum_at_most_except_one (localIndependence G) 3 2 b two (fun y _=>cap y)
  omega

#print axioms small_core_four_base
#print axioms small_core_min_three_case
universe w

/-- On four through nine vertices a C4-free graph has ten units of
signed slack below local-independence mean four. -/
theorem small_core_ten_signed_slack_aux (n : Nat) :
    ∀ {U : Type w} [Fintype U] [DecidableEq U] (J : SimpleGraph U) [DecidableRel J.Adj],
      Fintype.card U=n→4≤n→n≤9→FourCycleFree J→
        (∑ x : U,localIndependence J x)+10≤4*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U fi de J dec eq lo hi h4
    classical
    letI : DecidableRel J.Adj := Classical.decRel _
    by_cases n4 : n=4
    · have base := small_core_four_base h4 (eq.trans n4)
      omega
    by_cases low : ∃ x : U,J.degree x≤2
    · obtain ⟨x,dx⟩ := low
      let T := (Finset.univ : Finset U).erase x
      let K := J.induce (T : Set U)
      have tc : T.card=n-1 := by
        simp [T,Finset.card_erase_of_mem,eq]
      have kc : Fintype.card (T : Set U)=n-1 := (Fintype.card_coe T).trans tc
      have k4 : FourCycleFree K := by
        intro a b z w ne az bz aw bw
        exact Subtype.ext (h4 a.val b.val z.val w.val (fun e=>ne (Subtype.ext e)) az bz aw bw)
      have sub := ih (n-1) (by omega) K kc (by omega) (by omega) k4
      have eqQ : (Finset.univ : Finset U)\T={x} := by
        ext v
        simp [T]
      have fj : T.filter (J.Adj x)=J.neighborFinset x := by
        ext v
        simp only [T,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,small_mem_neighbor]
        exact ⟨fun e=>e.2,fun e=>⟨e.ne.symm,e⟩⟩
      have s := core_and_exterior_independence_sum (G:=J) T
      change _ ≤ (∑ v : (T : Set U),localIndependence K v)+
        (∑ q∈(Finset.univ : Finset U)\T,localIndependence J q)+
        (∑ q∈(Finset.univ : Finset U)\T,(T.filter (J.Adj q)).card) at s
      rw [eqQ,Finset.sum_singleton,Finset.sum_singleton,fj,J.card_neighborFinset_eq_degree] at s
      have le := small_local_le_degree (G:=J) x
      omega
    have dmin (x : U) : 3≤J.degree x := by
      by_cases bad : J.degree x≤2
      · exact (low ⟨x,bad⟩).elim
      omega
    have z := small_core_min_three_case h4 (by omega) (by omega) dmin
    rwa [eq] at z

theorem small_core_ten_signed_slack (lo : 4≤Fintype.card V) (hi : Fintype.card V≤9)
    (h4 : FourCycleFree G) : (∑ x : V,localIndependence G x)+10≤4*Fintype.card V :=
  small_core_ten_signed_slack_aux _ G rfl lo hi h4

#print axioms small_core_ten_signed_slack
end Graffiti133P5CliqueArms
