import ShoreRanks
namespace Graffiti384b.OddStars.FixedCubics
open Finset SimpleGraph LeafCritical ShorePairs ShoreRanks
open private Repair.triangles_le_choose from Repair384b
open private Graffiti384b.cut from Proof384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
theorem full_neighbors {v : V} (d : H.degree v=3) (s : trianglesAt H v=3)
    {p q : V} (vp : H.Adj v p) (vq : H.Adj v q) (ne : p≠q) : H.Adj p q := by
  let S := (H.neighborFinset v).powersetCard 2
  let T := S.filter (fun k => ∀ x∈k,∀ y∈k,x≠y → H.Adj x y)
  have st : S.card=3 := by simp only [S,card_powersetCard,card_neighborFinset_eq_degree,d]; decide
  have tt : T.card=3 := s
  have eq : T=S := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have pair : ({p,q} : Finset V)∈S := mem_powersetCard.mpr
    ⟨insert_subset ((H.mem_neighborFinset _ _).mpr vp) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr vq)),card_pair ne⟩
  have all := (mem_filter.mp (show ({p,q} : Finset V)∈T from eq ▸ pair)).2
  exact all p (mem_insert_self ..) q (mem_insert_of_mem (mem_singleton_self _)) ne


private theorem separated {u v : V} (du : H.degree u=3) (dv : H.degree v=3)
    (su : trianglesAt H u=2) (sv : trianglesAt H v=3) : ¬H.Adj u v := by
  intro uv
  let R := (H.neighborFinset v).erase u
  have um := (H.mem_neighborFinset ..).mpr uv.symm
  have rc : R.card=2 := by dsimp only [R]; rw [card_erase_of_mem um,card_neighborFinset_eq_degree,dv]
  have ur : u∉R := not_mem_erase u (H.neighborFinset v) 
  have vr : v∉R := fun h => (H.mem_neighborFinset ..).mp (mem_of_mem_erase h) |> fun edge => edge.ne rfl
  have Nr : H.neighborFinset v=insert u R := (insert_erase um).symm
  have adj (w : V) (wr : w∈R) : H.Adj u w :=
    full_neighbors H dv sv uv.symm ((H.mem_neighborFinset ..).mp (mem_of_mem_erase wr)) (mem_erase.mp wr).1.symm
  have sub : insert v R⊆H.neighborFinset u := insert_subset ((H.mem_neighborFinset ..).mpr uv)
    (fun w wm => (H.mem_neighborFinset ..).mpr (adj w wm))
  have Nu := (eq_of_subset_of_card_le sub (by rw [card_insert_of_not_mem vr,rc,card_neighborFinset_eq_degree,du])).symm
  have x : nbr H u R=R.card := by unfold nbr; rw [filter_eq_self.mpr adj]
  have y : nbr H v R=R.card := by
    unfold nbr
    rw [filter_eq_self.mpr (fun _ h => (H.mem_neighborFinset ..).mp (mem_of_mem_erase h))]
  change (pairs H (H.neighborFinset u)).card=2 at su
  change (pairs H (H.neighborFinset v)).card=3 at sv
  rw [Nu,pairs_insert H vr,y] at su
  rw [Nr,pairs_insert H ur,x] at sv
  omega

private theorem cubic_range (G : SimpleGraph V) [DecidableRel G.Adj] {x : V}
    (deg : (patch G ∅).degree x=3) : 2≤trianglesAt G x ∧ trianglesAt G x≤3 := by
  have lo := skeleton_degree_bound G x
  have hi := Repair.triangles_le_choose (patch G ∅) x
  rw [deg,patch_scores] at hi
  rw [deg] at lo
  have : Nat.choose 3 2=3 := by decide
  omega

/-- Exactly two vertices of the triangle skeleton are cubic. They have scores
two and three, are nonadjacent in the skeleton, and are precisely the two
critical vertices of every maximum cut. -/
theorem fixed_pair (G : SimpleGraph V) [DecidableRel G.Adj] (bad : bound G<gamma G)
    (size : (high (patch G ∅)).card+1=(types G).card) (has : (high (patch G ∅)).Nonempty) :
    ∃u v : V,u≠v ∧ trianglesAt G u=2 ∧ trianglesAt G v=3 ∧ ¬(patch G ∅).Adj u v ∧
      (∀x,(patch G ∅).degree x=3 ↔ x=u ∨ x=v) ∧
      ∀A : Finset V, Maximum (patch G ∅) A → critical (patch G ∅) A={u,v} := by
  classical
  let J := patch G ∅
  obtain ⟨A,_,m⟩ := exists_max_image (univ : Finset (Finset V)) (fun A => Graffiti384b.cut J A Aᶜ) univ_nonempty
  have mx : Maximum J A := fun S => m S (mem_univ _)
  have two := exactly_two_critical G bad size has mx
  obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp two
  have xc : x∈critical J A := eq ▸ mem_insert_self ..
  have yc : y∈critical J A := eq ▸ mem_insert_of_mem (mem_singleton_self _)
  have dx := critical_cubic G bad size mx xc
  have dy := critical_cubic G bad size mx yc
  have rx := cubic_range G dx
  have ry := cubic_range G dy
  have diff : trianglesAt G x≠trianglesAt G y := fun eq => xy (distinct_rich G bad rx.1 eq)
  obtain ⟨u,v,uv,du,dv,su,sv⟩ : ∃u v : V,u≠v ∧ J.degree u=3 ∧ J.degree v=3 ∧
      trianglesAt G u=2 ∧ trianglesAt G v=3 := by
    by_cases xx : trianglesAt G x=2
    · exact ⟨x,y,xy,dx,dy,xx,by omega⟩
    · exact ⟨y,x,xy.symm,dy,dx,by omega,by omega⟩
  have char (w : V) : J.degree w=3 ↔ w=u ∨ w=v := by
    constructor
    · intro d
      have r := cubic_range G d
      by_cases low : trianglesAt G w=2
      · exact Or.inl (distinct_rich G bad r.1 (low.trans su.symm))
      · exact Or.inr (distinct_rich G bad r.1 (by omega))
    · rintro (rfl|rfl) <;> assumption
  refine ⟨u,v,uv,su,sv,separated J du dv ((patch_scores G ∅ u).trans su) ((patch_scores G ∅ v).trans sv),char,?_⟩
  intro B opt
  apply eq_of_subset_of_card_le (fun w wm => by
    have c := (char w).mp (critical_cubic G bad size opt wm)
    simpa only [mem_insert,mem_singleton] using c)
  rw [card_pair uv,exactly_two_critical G bad size has opt]

end Graffiti384b.OddStars.FixedCubics
#print axioms Graffiti384b.OddStars.FixedCubics.fixed_pair
