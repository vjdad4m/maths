import Protected180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
universe u
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nonbip_order (G : SimpleGraph V) (bi : ¬TwoColor G univ) : bipartiteNum G<Fintype.card V := by
  obtain ⟨Z,col,mx⟩ := optB G
  by_contra! cap
  have eq := eq_univ_of_card Z (le_antisymm (card_le_univ _) (mx.symm ▸ cap))
  exact bi (eq ▸ col)

theorem bip_of_short (G : SimpleGraph V) (hn : 1<Fintype.card V) (small : Fintype.card V≤2) : TwoColor G univ := by
  obtain ⟨x,y,ne⟩ := Fintype.one_lt_card_iff.mp hn
  have un : ({x,y}:Finset V)=univ := eq_univ_of_card _ (by rw [card_pair ne];omega)
  exact ⟨{x},{y},by simp [ne,ne.symm],by simpa using un,by simp [Indep],by simp [Indep]⟩

theorem apex_of_rank_one (G : SimpleGraph V) (non : ¬TwoColor G univ) (rk : Fintype.card V≤bipartiteNum G+1) :
    ∃ t,TwoColor G (univ.erase t) := by
  classical
  obtain ⟨Z,col,mx⟩ := optB G
  have cnt := card_sdiff_add_card_eq_card (subset_univ Z)
  rw [card_univ] at cnt
  have lt := nonbip_order G non
  obtain ⟨t,one⟩ := card_eq_one.mp (show (univ\Z).card=1 by omega)
  have eq : univ.erase t=Z := by
    ext x
    have mem := Finset.ext_iff.mp one x
    simp only [mem_sdiff,mem_univ,true_and,mem_singleton] at mem
    simp only [mem_erase,mem_univ,and_true];tauto
  exact ⟨t,eq ▸ col⟩

/-- Both markings are paid by one bipartite witness even when the
unique available transversal vertex is protected. -/
theorem protected_rank_one (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+1) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) :
    Protected G r p A := by
  classical
  by_cases bi : TwoColor G univ
  · exact protected_bip G gc hn bi r p A ai
  have high : 2<Fintype.card V := by by_contra! small;exact bi (bip_of_short G hn small)
  have lt := nonbip_order G bi
  have reserve := rank_allowance G gc hn (by omega) r p A ai
  obtain ⟨t,col⟩ := apex_of_rank_one G bi rk
  let K := A∩insert r (parity G r p)
  apply (protected_iff G gc hn r p A ai).mpr
  by_cases tk : t∈K
  · have pay := protected_degree G gc high r t p A ai tk
    have ki : Indep G K := fun x xm y ym => ai x (mem_inter.mp xm).1 y (mem_inter.mp ym).1
    obtain ⟨Z,c,keep,cost⟩ := one_repair G t K ki tk col
    exact ⟨Z,c,keep,by omega⟩
  · refine ⟨univ.erase t,col,fun x xm => mem_erase.mpr ⟨fun eq => tk (eq ▸ xm),mem_univ _⟩,?_⟩
    rw [card_erase_of_mem (mem_univ _),card_univ];omega

/-- The two exact prime tests, including the odd-root test, hold on every
connected graph of order at least two having odd-cycle transversal number
at most one, at every root. -/
theorem prime_tests_rank_one (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+1) (r : V) : PrimeTests G r :=
  protected_tests G r (protected_rank_one G gc hn rk r)

/-- Only prime graphs with odd-cycle transversal number at least two need
the two rooted tests. -/
theorem universal_iff_prime_deficit_two_or_more : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → bipartiteNum G+1<Fintype.card W →
      ∀ r,(∀ y,¬DomEdge G r y) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc high _ _ r no;exact universal_prime_tests all G gc high r no
  · intro rest
    apply universal_iff_prime_tests.mpr
    intro W _ _ G gc high prime r no
    by_cases rk : Fintype.card W≤bipartiteNum G+1
    · exact prime_tests_rank_one G gc (by omega) rk r
    · exact rest W G gc high prime (by omega) r no

#print axioms apex_of_rank_one
#print axioms protected_rank_one
#print axioms prime_tests_rank_one
#print axioms universal_iff_prime_deficit_two_or_more
end Minimal180.Transversals
