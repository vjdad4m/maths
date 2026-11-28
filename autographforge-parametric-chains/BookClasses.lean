import ChainClasses
import ChordalBasis

namespace TwinForcing
open SimpleGraph Finset

private def hubRank {n : ℕ} (v : Fin n × Bool) := 2*v.1.val + v.2.toNat

private theorem hubRank_inj {n : ℕ} : Function.Injective (@hubRank n) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  cases b <;> cases c <;> simp [hubRank] at h
  · exact Prod.ext (Fin.ext (by change i.val = j.val; omega)) rfl
  · omega
  · omega
  · exact Prod.ext (Fin.ext (by change i.val = j.val; omega)) rfl

private theorem hubRank_lt {n : ℕ} (v : Fin n × Bool) : hubRank v < 2*n := by
  rcases v with ⟨i,b⟩
  have := i.isLt
  cases b <;> (simp [hubRank] <;> omega)

private theorem hubRank_adj {n : ℕ} {v w : Fin n × Bool}
    (e : (chainHubs n true).Adj v w) :
    hubRank v + 1 = hubRank w ∨ hubRank w + 1 = hubRank v := by
  change chainHubAdj true v w at e
  rcases e with ⟨_,i,h⟩|⟨b,c,k⟩|⟨b,c,k⟩
  · simp only [hubRank,i]
    generalize v.2 = b at *
    generalize w.2 = c at *
    cases b <;> cases c <;> simp_all
  · left
    simp [hubRank,b,c]
    omega
  · right
    simp [hubRank,b,c]
    omega

private def bookRank {n m : ℕ} : PageVertex n m → ℕ
  | .inl v => hubRank v
  | .inr _ => 2*n

private abbrev B (n m : ℕ) := chainGraph n m true

private def earlier {n m : ℕ} (x : PageVertex n m) : Finset (PageVertex n m) :=
  univ.filter (fun y => (B n m).Adj x y ∧ bookRank y ≤ bookRank x)

private theorem earlier_hub_unique {n m : ℕ} {u : Fin n × Bool} {v w : PageVertex n m}
    (hv : v ∈ earlier (.inl u)) (hw : w ∈ earlier (.inl u)) : v = w := by
  obtain ⟨ev,rv⟩ := (mem_filter.mp hv).2
  obtain ⟨ew,rw⟩ := (mem_filter.mp hw).2
  cases v with
  | inr v => exact (not_le_of_gt (hubRank_lt u) rv).elim
  | inl v =>
    cases w with
    | inr w => exact (not_le_of_gt (hubRank_lt u) rw).elim
    | inl w =>
      change hubRank v ≤ hubRank u at rv
      change hubRank w ≤ hubRank u at rw
      exact congrArg Sum.inl (hubRank_inj (by
        have a := hubRank_adj ev
        have b := hubRank_adj ew
        omega))

private theorem earlier_isClique {n m : ℕ} (x : PageVertex n m) :
    (B n m).IsClique (earlier x : Set (PageVertex n m)) := by
  intro v hv w hw neq
  cases x with
  | inl u => exact (neq (earlier_hub_unique hv hw)).elim
  | inr x =>
    obtain ⟨ev,_⟩ := (mem_filter.mp hv).2
    obtain ⟨ew,_⟩ := (mem_filter.mp hw).2
    rcases v with ⟨i,b⟩|v
    · rcases w with ⟨j,c⟩|w
      · change i = x.1 at ev
        change j = x.1 at ew
        have k := ev.trans ew.symm
        change chainHubAdj true (i,b) (j,c)
        exact Or.inl ⟨rfl,k,by intro bc; exact neq (congrArg Sum.inl (Prod.ext k bc))⟩
      · exact ew.elim
    · exact ev.elim

theorem book_chain_chordal (n m : ℕ) : TriangleChain.Chordal (B n m) := by
  apply TriangleChain.chordal_of_elimination _ bookRank
  intro x y z xy xz ne ry rz
  exact earlier_isClique x (mem_filter.mpr ⟨mem_univ _,xy,ry⟩)
    (mem_filter.mpr ⟨mem_univ _,xz,rz⟩) ne

private theorem earlier_bound {n m : ℕ} (x : PageVertex n m) :
    (earlier x).card ≤ 2 := by
  rcases x with x | ⟨i,p⟩
  · exact (Finset.card_le_one.mpr fun _ hv _ hw => earlier_hub_unique hv hw).trans (by decide)
  · have sub : earlier (.inr (i,p)) ⊆ (B n m).neighborFinset (.inr (i,p)) := by
      intro y hy
      exact (mem_neighborFinset _ _ _).mpr (mem_filter.mp hy).2.1
    exact (card_le_card sub).trans (le_of_eq (page_degree (chainHubs n true) i p))

theorem book_chain_k4_free (n m : ℕ) : (B n m).CliqueFree 4 := by
  intro S hS
  obtain ⟨hcl,hcard⟩ := (B n m).isNClique_iff.mp hS
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x,hx,best⟩ := Finset.exists_max_image S bookRank hn
  have sub : S.erase x ⊆ earlier x := by
    intro y hy
    obtain ⟨ne,hy'⟩ := mem_erase.mp hy
    exact mem_filter.mpr ⟨mem_univ _,hcl hx hy' ne.symm,best y hy'⟩
  have le := (card_le_card sub).trans (earlier_bound x)
  rw [card_erase_of_mem hx,hcard] at le
  omega

theorem book_gap_unbounded (M : ℕ) :
    ∃ (G : SimpleGraph (PageVertex (M+3) (4*M+9))) (dec : DecidableRel G.Adj),
      G.Connected ∧ G.CliqueFree 4 ∧ TriangleChain.Chordal G ∧
      Graffiti324.residue G + M < @StarCone.forcing _ _ _ G dec 2 := by
  let G := B (M+3) (4*M+9)
  refine ⟨G,inferInstance,chain_connected (by omega) (by omega) true,
    book_chain_k4_free _ _,book_chain_chordal _ _,?_⟩
  rw [show StarCone.forcing G 2 = graphResidue G + (2*M*M+7*M+4) from
    book_chain_forcing_excess M, graphResidue_eq_residue]
  omega

#print axioms book_chain_chordal
#print axioms book_chain_k4_free
#print axioms book_gap_unbounded
end TwinForcing
