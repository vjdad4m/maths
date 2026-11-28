import Restrained
import OuterForest

namespace JoinOuter500
open SimpleGraph Finset CographRadius Restrained534 AutoGraphForge370
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem maximum_dominates {S : Finset V} (hS : G.IsMaximumIndepSet S) : Dominates G S := by
  classical
  intro v
  by_contra! missed
  have larger : G.IsIndepSet (↑(insert v S : Finset V) : Set V) := by
    intro a ha b hb ne ab
    rcases mem_insert.mp ha with rfl|aS <;> rcases mem_insert.mp hb with rfl|bS
    · exact ne rfl
    · exact missed.2 b bS ab
    · exact missed.2 a aS ab.symm
    · exact hS.isIndepSet aS bS ne ab
  have bound := hS.maximum _ larger
  rw [card_insert_of_not_mem missed.1] at bound
  omega

omit [Fintype V] in
theorem outside_center {D : Finset V} {u : V} (hu : u ∉ D)
    (hall : ∀ x ∉ D, x ≠ u → G.Adj x u) :
    (G.induce (D : Set V)ᶜ).Connected := by
  let c : ↥((D : Set V)ᶜ) := ⟨u, hu⟩
  have reach (x : ↥((D : Set V)ᶜ)) :
      (G.induce (D : Set V)ᶜ).Reachable x c := by
    by_cases h : (x : V) = u
    · have hx : x = c := Subtype.ext h
      subst x; exact .rfl
    · exact (show (G.induce (D : Set V)ᶜ).Adj x c from hall x x.property h).reachable
  letI : Nonempty ↥((D : Set V)ᶜ) := ⟨c⟩
  exact ⟨fun a b => (reach a).trans (reach b).symm⟩

theorem pair_lower {a b : V} (h : a ≠ b) (e : ¬ G.Adj a b) : 2 ≤ G.indepNum := by
  classical
  have hI : G.IsIndepSet (↑({a,b} : Finset V) : Set V) := by
    intro x hx y hy ne exy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact ne rfl
    · exact e exy
    · exact e exy.symm
    · exact ne rfl
  simpa [h] using hI.card_le_indepNum

theorem exists_outer [Nontrivial V] (conn : G.Connected) (cog : Cograph G) :
    ∃ D : Finset V, OuterDominating G D ∧ D.card ≤ G.indepNum := by
  classical
  obtain ⟨S,hS⟩ := maximumIndepSet_exists (G := G)
  have eqS : S.card = G.indepNum := maximumIndepSet_card_eq_indepNum S hS
  have dom := maximum_dominates G hS
  by_cases low : G.indepNum < 2
  · have all (a b : V) (h : a ≠ b) : G.Adj a b := by
      apply Classical.byContradiction
      intro ne
      exact (not_le_of_gt low) (pair_lower G h ne)
    obtain ⟨a,b,ab⟩ := exists_pair_ne V
    let D : Finset V := {a}
    have aDom : ∀ x ∉ D, ∃ y ∈ D, G.Adj x y := by
      intro x hx
      exact ⟨a,by simp [D],all x a (by simpa [D] using hx)⟩
    have card0 : 1 ≤ G.indepNum := by
      have hs : G.IsIndepSet (↑({a} : Finset V) : Set V) := by
        intro x hx y hy ne _
        simp only [coe_singleton,Set.mem_singleton_iff] at hx hy
        exact ne (hx.trans hy.symm)
      simpa using hs.card_le_indepNum
    exact ⟨D, ⟨aDom, outside_center G (D:=D) (u:=b) (by simp [D,ab.symm])
      (fun x _ ne => all x b ne)⟩, by simpa [D] using card0⟩
  by_cases uni : ∃ u, Universal G u
  · obtain ⟨u,hu⟩ := uni
    have notmem : u ∉ S := by
      intro yes
      have sub : S ⊆ {u} := by
        intro x hx
        apply mem_singleton.mpr
        apply Classical.byContradiction
        intro ne
        exact hS.isIndepSet yes hx (fun e => ne e.symm) (hu x (fun e => ne e.symm))
      have small := card_le_card sub
      simp only [card_singleton,eqS] at small
      omega
    exact ⟨S, ⟨fun x hx => (dom x).resolve_left hx,
      outside_center G notmem (fun x _ ne => (hu x ne.symm).symm)⟩, eqS.le⟩
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨A,a,b,ha,hb,cross⟩ := cograph_join G conn cog
  have missing (v : V) : ∃ w, v ≠ w ∧ ¬ G.Adj v w := by
    apply Classical.byContradiction
    intro hh
    push_neg at hh
    exact uni ⟨v,hh⟩
  obtain ⟨a',aa',ma⟩ := missing a
  obtain ⟨b',bb',mb⟩ := missing b
  have ha' : A a' := by
    apply Classical.byContradiction
    intro hh
    exact ma (cross a a' ha hh)
  have hb' : ¬ A b' := fun h => mb (cross b' b h hb).symm
  have ab : a ≠ b := fun e => hb (e ▸ ha)
  let D : Finset V := {a,b}
  have outA : a' ∉ D := by simp [D,aa'.symm,show a' ≠ b from fun e => hb (e ▸ ha')]
  have outB : b' ∉ D := by simp [D,bb'.symm,show b' ≠ a from fun e => hb' (e.symm ▸ ha)]
  let x' : ↥((D : Set V)ᶜ) := ⟨a', outA⟩
  let y' : ↥((D : Set V)ᶜ) := ⟨b', outB⟩
  have bridge : (G.induce (D : Set V)ᶜ).Adj y' x' := (cross a' b' ha' hb').symm
  have reach (x : ↥((D : Set V)ᶜ)) :
      (G.induce (D : Set V)ᶜ).Reachable x x' := by
    by_cases hx : A x
    · have e : (G.induce (D : Set V)ᶜ).Adj x y' := cross x b' hx hb'
      exact e.reachable.trans bridge.reachable
    · have e : (G.induce (D : Set V)ᶜ).Adj x x' := (cross a' x ha' hx).symm
      exact e.reachable
  letI : Nonempty ↥((D : Set V)ᶜ) := ⟨x'⟩
  refine ⟨D,⟨?_,⟨fun x y => (reach x).trans (reach y).symm⟩⟩,?_⟩
  · intro v _
    by_cases h : A v
    · exact ⟨b,by simp [D],cross v b h hb⟩
    · exact ⟨a,by simp [D],(cross a v ha h).symm⟩
  · simpa [D,ab] using (le_of_not_gt low : 2 ≤ G.indepNum)

theorem row500 (hn : 2 ≤ Fintype.card V) (conn : G.Connected) (cog : Cograph G) :
    ∃ k, outerNumber G = some k ∧ k ≤ G.indepNum := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨D,hD,hcard⟩ := exists_outer G conn cog
  unfold outerNumber
  split
  · rename_i h
    exact ⟨Nat.find h,rfl,(Nat.find_min' h ⟨D,hD,rfl⟩).trans hcard⟩
  · rename_i h
    exact (h ⟨D.card,D,hD,rfl⟩).elim

#print axioms row500
end JoinOuter500
