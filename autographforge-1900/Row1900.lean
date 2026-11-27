import Criterion
import DegreeTwo

namespace OuterStar1900
open Finset SimpleGraph AutoGraphForge370 CubicBridges1160
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A center with independent neighbors, all of degree at least two, can
be left outside a dominating set along with all but one of its neighbors. -/
theorem star_complement (v : V) (pos : 0 < G.degree v)
    (independent : ∀ x y, G.Adj v x → G.Adj v y → ¬ G.Adj x y)
    (neighbors : ∀ x, G.Adj v x → 2 ≤ G.degree x) :
    ∃ D : Finset V, OuterDominating G D ∧ D.card + G.degree v = Fintype.card V := by
  classical
  obtain ⟨w,vw⟩ := (G.degree_pos_iff_exists_adj v).mp pos
  let N := G.neighborFinset v
  let C := insert v (N.erase w)
  let D := univ \ C
  have inside (x : V) : x ∉ D ↔ x ∈ C := by simp [D]
  have parts (x : V) : x ∈ C ↔ x = v ∨ (x ≠ w ∧ G.Adj v x) := by simp [C,N]
  have dom : OuterDominating G D := by
    constructor
    · intro x hx
      rcases (parts x).mp ((inside x).mp hx) with rfl | ⟨_,vx⟩
      · exact ⟨w,by simp [D,parts,vw.ne.symm],vw⟩
      · obtain ⟨u,hu,ne⟩ := exists_mem_ne (s := G.neighborFinset x)
          (show 1 < (G.neighborFinset x).card from neighbors x vx) v
        have xu := (G.mem_neighborFinset _ _).mp hu
        have out : u ∉ C := fun hc => by
          rcases (parts u).mp hc with eq | ⟨_,vu⟩
          · exact ne eq
          · exact independent x u vx vu xu
        exact ⟨u,by simp [D,out],xu⟩
    · apply (connected_iff_exists_forall_reachable _).mpr
      let z : ↥((D : Set V)ᶜ) := ⟨v,(inside v).mpr ((parts v).mpr (Or.inl rfl))⟩
      refine ⟨z,?_⟩
      rintro ⟨x,hx⟩
      rcases (parts x).mp ((inside x).mp hx) with rfl | ⟨_,vx⟩
      · exact Reachable.rfl
      · exact (show (G.induce (D : Set V)ᶜ).Adj z ⟨x,hx⟩ from vx).reachable
  have nv : v ∉ N := by simp [N]
  have nw : w ∈ N := (G.mem_neighborFinset _ _).mpr vw
  have cv : C.card = G.degree v := by
    change (insert v (N.erase w)).card = N.card
    rw [card_insert_of_not_mem (fun h => nv (mem_of_mem_erase h)),card_erase_of_mem nw]
    have := card_pos.mpr (show N.Nonempty from ⟨w,nw⟩)
    omega
  refine ⟨D,dom,?_⟩
  simpa only [D,cv,card_univ] using card_sdiff_add_card_eq_card (subset_univ C)

/-- The degree of a maximal center can replace the minimum degree in the
triangle-free bound. The ambient graph need not be connected. -/
theorem max_degree_bound [Nonempty V] (triangle : TriangleFree G) (minTwo : ∀ v, 2 ≤ G.degree v) :
    ∃ o, outerNumber G = some o ∧ o + G.maxDegree ≤ Fintype.card V := by
  obtain ⟨v,deg⟩ := G.exists_maximal_degree_vertex
  obtain ⟨D,valid,sz⟩ := star_complement G v (by have := minTwo v; omega)
    (fun x y vx vy xy => triangle v x y vx xy vy.symm) (fun x _ => minTwo x)
  classical
  have ex : ∃ n, ∃ S : Finset V, OuterDominating G S ∧ S.card = n :=
    ⟨D.card,D,valid,rfl⟩
  have small := Nat.find_min' ex (show ∃ S : Finset V, OuterDominating G S ∧ S.card=D.card from
    ⟨D,valid,rfl⟩)
  exact ⟨Nat.find ex,by simp [outerNumber,dif_pos ex],by omega⟩

omit [DecidableRel G.Adj] in
theorem triangle_cover (triangle : TriangleFree G) : Fintype.card V ≤ 2 * cliqueCover G := by
  classical
  obtain ⟨col⟩ := cover_attained G
  let F (i : Fin (cliqueCover G)) := univ.filter (fun x => col x = i)
  have count : Fintype.card V = ∑ i, (F i).card :=
    card_eq_sum_card_fiberwise (s:=univ) (t:=univ) (f:=fun v : V => col v) (by simp)
  rw [count]
  calc ∑ i, (F i).card ≤ ∑ _i : Fin (cliqueCover G), 2 :=
        sum_le_sum (fun i _ => fiber_small G triangle col i)
       _ = _ := by simp [Nat.mul_comm]

private theorem eulerian_min_two (order : 2 ≤ Fintype.card V) (conn : G.Connected)
    (even : ∀ v, Even (G.degree v)) (v : V) : 2 ≤ G.degree v := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp order
  have pos : 0 < G.degree v := by
    apply (G.degree_pos_iff_exists_adj v).mpr
    obtain ⟨w,diff⟩ := exists_ne v
    obtain ⟨walk⟩ := conn.preconnected v w
    cases walk with
    | nil => exact (diff rfl).elim
    | cons e _ => exact ⟨_,e⟩
  obtain ⟨a,ha⟩ := even v
  omega

/-- Physical row 1900, with the catalogue's signed subtraction. -/
theorem row1900 (order : 2 ≤ Fintype.card V) (conn : G.Connected)
    (even : ∀ v, Even (G.degree v)) (triangle : TriangleFree G) :
    ∃ o, outerNumber G = some o ∧ (o : ℤ) ≤ 2 * (cliqueCover G : ℤ) + (-2) := by
  haveI := conn.nonempty
  have deg := eulerian_min_two G order conn even
  obtain ⟨o,ho,cap⟩ := max_degree_bound G triangle deg
  obtain ⟨v,eq⟩ := G.exists_maximal_degree_vertex
  have lo := deg v
  have total := triangle_cover G triangle
  exact ⟨o,ho,by omega⟩

/-- Equality in the row is equivalent to degree two everywhere and a perfect
matching. This equivalence only needs minimum degree two and triangle-freeness. -/
theorem equality_criterion [Nonempty V] (triangle : TriangleFree G)
    (minTwo : ∀ v, 2 ≤ G.degree v) {o : ℕ} (val : outerNumber G = some o) :
    o+2 = 2*cliqueCover G ↔ G.IsRegularOfDegree 2 ∧ ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨p,hp,cap⟩ := max_degree_bound G triangle minTwo
  have id := Option.some.inj (hp.symm.trans val)
  subst p
  have total := triangle_cover G triangle
  constructor
  · intro tight
    constructor
    · intro v
      have := G.degree_le_maxDegree v
      have := minTwo v
      omega
    · apply perfect_of_half G triangle
      obtain ⟨v,eq⟩ := G.exists_maximal_degree_vertex
      have := minTwo v
      omega
  · rintro ⟨reg,M,pm⟩
    have half := half_of_perfect G pm
    classical
    unfold outerNumber at val
    split at val
    · rename_i ex
      cases val
      obtain ⟨D,hd,sz⟩ := Nat.find_spec ex
      have budget := outer_budget G (fun v => (reg v).le) D hd
      obtain ⟨v,eq⟩ := G.exists_maximal_degree_vertex
      have := minTwo v
      omega
    · contradiction

#print axioms star_complement
#print axioms max_degree_bound
#print axioms triangle_cover
#print axioms row1900
#print axioms equality_criterion
end OuterStar1900
