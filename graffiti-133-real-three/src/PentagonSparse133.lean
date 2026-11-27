import PentagonEar133
import PentagonBudget133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

private def reindex (π : Fin 5 ≃ Fin 5)
    (h : ∀ i j, pent (π i) (π j) ↔ pent i j) : PentagonFrame G where
  c i := F.c (π i)
  inj := F.inj.comp π.injective
  adj i j := (F.adj _ _).trans (h i j)
  h4 := F.h4
  noP6 := F.noP6
  dom := by
    intro x out
    have out' : Outside F.c x := by
      intro i
      obtain ⟨j,rfl⟩ := π.surjective i
      exact out j
    obtain ⟨i,hi⟩ := F.dom x out'
    obtain ⟨j,rfl⟩ := π.surjective i
    exact ⟨j,hi⟩

private theorem one_reindex (π : Fin 5 ≃ Fin 5)
    (h : ∀ i j, pent (π i) (π j) ↔ pent i j) {x : V} {k : Fin 5}
    (hx : One G F.c x (π k)) : One G (F.reindex π h).c x k := by
  refine ⟨fun i => hx.1 (π i),fun j => (hx.2 (π j)).trans ?_⟩
  exact π.injective.eq_iff

private theorem two_reindex (π : Fin 5 ≃ Fin 5)
    (h : ∀ i j, pent (π i) (π j) ↔ pent i j) {x : V} {k : Fin 5}
    (hs : π (k+1) = π k + 1) (hx : Two G F.c x (π k)) :
    Two G (F.reindex π h).c x k := by
  refine ⟨fun i => hx.1 (π i),fun j => (hx.2 (π j)).trans ?_⟩
  rw [← hs, π.injective.eq_iff, π.injective.eq_iff]

private def rot (a : Fin 5) : Fin 5 ≃ Fin 5 where
  toFun i := a+i
  invFun i := i-a
  left_inv := ((by decide : ∀ a i : Fin 5, (a+i)-a=i) a)
  right_inv := ((by decide : ∀ a i : Fin 5, a+(i-a)=i) a)

private def refl (a : Fin 5) : Fin 5 ≃ Fin 5 where
  toFun i := a-i
  invFun i := a-i
  left_inv := ((by decide : ∀ a i : Fin 5, a-(a-i)=i) a)
  right_inv := ((by decide : ∀ a i : Fin 5, a-(a-i)=i) a)

private lemma rot_pent : ∀ a i j, pent (rot a i) (rot a j) ↔ pent i j := by decide
private lemma refl_pent : ∀ a i j, pent (refl a i) (refl a j) ↔ pent i j := by decide
private lemma rot_zero : ∀ a, rot a 0 = a := by decide
private lemma refl_zero : ∀ a, refl a 0 = a := by decide
private lemma rot_two : ∀ a, rot a 2 = a+2 := by decide
private lemma refl_two : ∀ a, refl a 2 = a+3 := by decide
private lemma rot_next : ∀ a i, rot a (i+1) = rot a i+1 := by decide

private theorem ear_at_any_site {x y : V} {i : Fin 5} (hx : One G F.c x i)
    (hy : One G F.c y (i+2) ∨ One G F.c y (i+3) ∨ Two G F.c y (i+2))
    (e : G.Adj x y) : radius G ≤ 2 := by
  rcases hy with hy | hy | hy
  · apply (F.reindex (rot i) (rot_pent i)).anchored_ear_radius (x:=x) (y:=y) _ _ e
    · exact F.one_reindex _ _ ((rot_zero i).symm ▸ hx)
    · exact Or.inl (F.one_reindex _ _ ((rot_two i).symm ▸ hy))
  · apply (F.reindex (refl i) (refl_pent i)).anchored_ear_radius (x:=x) (y:=y) _ _ e
    · exact F.one_reindex _ _ ((refl_zero i).symm ▸ hx)
    · exact Or.inl (F.one_reindex _ _ ((refl_two i).symm ▸ hy))
  · apply (F.reindex (rot i) (rot_pent i)).anchored_ear_radius (x:=x) (y:=y) _ _ e
    · exact F.one_reindex _ _ ((rot_zero i).symm ▸ hx)
    · exact Or.inr (F.two_reindex _ _ (rot_next i 2) ((rot_two i).symm ▸ hy))

private lemma pair_slots : ∀ i j : Fin 5,
    (j = i ∨ j = i+2 ∨ j = i+3) → (j+1 = i ∨ j+1 = i+2 ∨ j+1 = i+3) →
    j = i+2 := by decide
private lemma next_diff : ∀ i : Fin 5, i ≠ i+1 := by decide

private theorem one_no_ear {x y : V} {i : Fin 5} (rad : 2 < radius G)
    (hx : One G F.c x i) (hy : Outside F.c y) (e : G.Adj x y) :
    One G F.c y i := by
  rcases F.classify_contact y hy with ⟨j,hj⟩ | ⟨j,hj⟩
  · rcases F.outside_to_one hx hy e ((hj.2 _).mpr rfl) with h | h | h
    · exact h ▸ hj
    · exact ((not_le_of_gt rad) (F.ear_at_any_site hx (Or.inl (h ▸ hj)) e)).elim
    · exact ((not_le_of_gt rad) (F.ear_at_any_site hx (Or.inr (Or.inl (h ▸ hj))) e)).elim
  · have j1 := F.outside_to_one hx hy e ((hj.2 _).mpr (Or.inl rfl))
    have j2 := F.outside_to_one hx hy e ((hj.2 _).mpr (Or.inr rfl))
    have eq := pair_slots i j j1 j2
    exact ((not_le_of_gt rad) (F.ear_at_any_site hx (Or.inr (Or.inr (eq ▸ hj))) e)).elim

private theorem outside_edge_same_single {x y : V} (rad : 2 < radius G)
    (hx : Outside F.c x) (hy : Outside F.c y) (e : G.Adj x y) :
    ∃ i, One G F.c x i ∧ One G F.c y i := by
  rcases F.classify_contact x hx with ⟨i,hi⟩ | ⟨i,hi⟩
  · exact ⟨i,hi,F.one_no_ear rad hi hy e⟩
  · rcases F.classify_contact y hy with ⟨j,hj⟩ | ⟨j,hj⟩
    · exact ⟨j,F.one_no_ear rad hj hx e.symm,hj⟩
    · have j1 := F.outside_to_two hi hy e ((hj.2 _).mpr (Or.inl rfl))
      have j2 := F.outside_to_two hi hy e ((hj.2 _).mpr (Or.inr rfl))
      exact (next_diff j (j1.trans j2.symm)).elim

private lemma one_two_no {x : V} {i j : Fin 5} (hi : One G F.c x i)
    (hj : Two G F.c x j) : False := by
  have ja := (hi.2 _).mp ((hj.2 _).mpr (Or.inl rfl))
  have jb := (hi.2 _).mp ((hj.2 _).mpr (Or.inr rfl))
  exact next_diff j (ja.trans jb.symm)

/-- If radius is above two, a P6-free C5 frame has local independence
at most one at every non-cycle vertex. -/
theorem sparse_outside (rad : 2 < radius G) {x : V} (hx : Outside F.c x) :
    localIndependence G x ≤ 1 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  apply Finset.card_le_one.mpr
  obtain ⟨hN,hI⟩ := memLocalSet.mp hA
  intro y hy z hz
  rcases F.classify_contact x hx with ⟨i,hi⟩ | ⟨i,hi⟩
  · have data (w : V) (e : G.Adj x w) : w = F.c i ∨ G.Adj w (F.c i) := by
      by_cases out : Outside F.c w
      · exact Or.inr ((F.one_no_ear rad hi out e).2 i |>.mpr rfl)
      · obtain ⟨j,hj⟩ : ∃ j, w = F.c j := by
          apply Classical.byContradiction
          intro bad
          exact out (fun j h => bad ⟨j,h⟩)
        have ji := (hi.2 j).mp (hj ▸ e)
        exact Or.inl (hj.trans (congrArg F.c ji))
    rcases data y (hN y hy) with ey | ey <;> rcases data z (hN z hz) with ez | ez
    · exact ey.trans ez.symm
    · exact (hI _ hy _ hz (ey.symm ▸ ez.symm)).elim
    · exact (hI _ hy _ hz (ez.symm ▸ ey)).elim
    · exact F.same_site_neighbors hx (hN _ hy) (hN _ hz) ey ez
  · have data (w : V) (e : G.Adj x w) : w = F.c i ∨ w = F.c (i+1) := by
      by_cases out : Outside F.c w
      · obtain ⟨j,hj,_⟩ := F.outside_edge_same_single rad hx out e
        exact (F.one_two_no hj hi).elim
      · obtain ⟨j,hj⟩ : ∃ j, w = F.c j := by
          apply Classical.byContradiction
          intro bad
          exact out (fun j h => bad ⟨j,h⟩)
        rcases (hi.2 j).mp (hj ▸ e) with j1 | j2
        · exact Or.inl (hj.trans (congrArg F.c j1))
        · exact Or.inr (hj.trans (congrArg F.c j2))
    have hh : G.Adj (F.c i) (F.c (i+1)) := (F.adj _ _).mpr (Or.inl rfl)
    rcases data y (hN y hy) with ey | ey <;> rcases data z (hN z hz) with ez | ez
    · exact ey.trans ez.symm
    · exact (hI _ hy _ hz (ey.symm ▸ ez.symm ▸ hh)).elim
    · exact (hI _ hy _ hz (ey.symm ▸ ez.symm ▸ hh.symm)).elim
    · exact ey.trans ez.symm

#print axioms sparse_outside

end PentagonFrame
end Graffiti133Pentagon
