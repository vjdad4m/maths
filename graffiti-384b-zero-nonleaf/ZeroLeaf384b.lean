import CycleSquareArms
import PendantAudit

namespace Graffiti384b.OddStars
open Finset SimpleGraph PositivePalette OneEar HallArms
open private OddStars.no_zero_neighbor from ZeroTwoLayout
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A degree-two zero and a positive representative can be simultaneously
accounted for: a hypothetical failure cannot have this degree at zero. -/
theorem degree_two_zero_bound {z : V} (zz : trianglesAt G z=0) (dz : G.degree z=2) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt
  intro bad
  classical
  let J := patch G {z}
  obtain ⟨e,_,one⟩ := mem_image.mp (zero_two_forces_ears G bad zz dz).1
  have ee := (zero_two_forces_ears G bad zz dz).2 e one
  have ez : e≠z := fun eq => by rw [eq,zz] at one; contradiction
  have noez : ¬J.Adj e z := fun h => OddStars.no_zero_neighbor G ee one zz h.1
  obtain ⟨a,b,c,d,na,nb,_,_,n,m,p,q,sep⟩ := failure_disjoint_arms G bad zz dz one
  have ea : J.Adj e a := (J.mem_neighborFinset ..).mp (na ▸ mem_insert_self ..)
  have eb : J.Adj e b := (J.mem_neighborFinset ..).mp (na ▸ mem_insert_of_mem (mem_singleton_self _))
  have zc : J.Adj z c := (J.mem_neighborFinset ..).mp (nb ▸ mem_insert_self ..)
  have zd : J.Adj z d := (J.mem_neighborFinset ..).mp (nb ▸ mem_insert_of_mem (mem_singleton_self _))
  let seed : Link J e z a b := ⟨c,d,zc,zd,n,m,p,q,sep⟩
  obtain ⟨L,np,mp,odd,uv,_,du⟩ := minimum_diamond G bad zz dz one ea eb ⟨seed⟩
  have cut := diamond_cut J L ez noez ea eb np mp odd uv du
  have eq := (high_description G bad zz dz {z}).1
  rw [eq] at cut
  have ret := count_covered G (covered_mono G (J:=J) (fun _ _ h => h.1) cut)
  have low (v : V) (deg : G.degree v=2) : v∉high G := fun vm => by have := (mem_filter.mp vm).2; omega
  rw [card_insert_of_not_mem (by simp [ez,low e ee]),card_insert_of_not_mem (low z dz)] at ret
  have tight := (two_frames G bad zz dz one).2.2.1
  omega

/-- At every order, every failure has only zero vertices of degree at most
one. This includes both parities and allows disconnected graphs. -/
theorem failure_zero_le_one (bad : bound G<gamma G) {z : V} (zz : trianglesAt G z=0) : G.degree z≤1 := by
  have cap := zero_degree G bad zz
  apply Nat.le_of_not_gt
  intro ge
  exact (not_lt_of_ge (degree_two_zero_bound G zz (by omega))) bad

/-- A realized zero on a nonleaf suffices for the full catalogue inequality. -/
theorem exact_of_zero_nonleaf {z : V} (zz : trianglesAt G z=0) (deg : 2≤G.degree z) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  have := failure_zero_le_one G bad zz
  omega

end Graffiti384b.OddStars
#print axioms Graffiti384b.OddStars.degree_two_zero_bound
#print axioms Graffiti384b.OddStars.failure_zero_le_one
#print axioms Graffiti384b.OddStars.exact_of_zero_nonleaf