import SaturatedPair180
import ReturnBudget180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The old optimum bounds the number of releases in terms of the remote
components. At equality each chosen return is needed by the scoring bound. -/
theorem gate_count_bound (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (sat : ∀ b∈C.erase x,J.Adj x b)
    (feed : ∀ z∈Z,Dominates J ((univ\C)\Z) z)
    (gates : ∀ H∈remote J ((univ\C)\Z) y,∃ z∈Z,∀ i∈H,∀ j∈Z,J.Adj i j → j=z) :
    Z.card≤(remote J ((univ\C)\Z) y).card+1 := by
  classical
  let R := (univ\C)\Z
  let K := remote J R y
  have zs' : Z⊆(univ\C).erase y := by
    intro t h
    obtain ⟨ty,tc⟩ := mem_erase.mp (zs h)
    exact mem_erase.mpr ⟨ty,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp tc).2⟩⟩
  have contact (H : Finset V) (h : H∈K) : ∃ b∈C.erase x,Dominates J H b :=
    contact_of_one_gate J C Z x y tip zs' nc H h (gates H h)
  let f (H : Finset V) := if h : H∈K then (contact H h).choose else x
  have hf (H : Finset V) (h : H∈K) : f H∈C.erase x ∧ Dominates J H (f H) := by
    simpa only [f,dif_pos h] using (contact H h).choose_spec
  let B := K.image f
  have bc : B⊆C.erase x := by
    intro b hb
    obtain ⟨H,h,rfl⟩ := mem_image.mp hb
    exact (hf H h).1
  have leB : B.card≤K.card := card_image_le
  apply le_trans _ (Nat.add_le_add_right leB 1)
  apply release_bound J hc hn x y w xy old xw wy U C B Z cu count tip bc zs (fun b h => sat b (bc h))
  · intro H h
    exact ⟨f H,mem_image_of_mem f h,(hf H h).2⟩
  · intro q h
    obtain ⟨z,nr,nx⟩ := (mem_demand ..).mp h
    rcases mem_union.mp z with qc|qz
    · exact (nx (sat q qc).symm).elim
    · exact (nr (feed q qz)).elim

/-- Exact pair repair when deletion leaves at most one remote component. -/
theorem pair_of_at_most_one (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y) (pair : Z.card=2)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (sat : ∀ b∈C.erase x,J.Adj x b)
    (feed : ∀ z∈Z,Dominates J ((univ\C)\Z) z)
    (atMost : (remote J ((univ\C)\Z) y).card≤1)
    (gates : ∀ H∈remote J ((univ\C)\Z) y,∃ z∈Z,∀ i∈H,∀ j∈Z,J.Adj i j → j=z) :
    FirstForm J U x y w ∧ ∃ b∈C.erase x, let L := (C.erase x).erase b ∪ Z
      L⊆U\{x,y} ∧ L.card=C.card ∧ L\C=Z ∧ C\L={x,b} ∧
      Con (J⊔SimpleGraph.edge x y) (univ\L) ∧ ∀ q∈L,Dominates (J⊔SimpleGraph.edge x y) (univ\L) q := by
  classical
  have lo := gate_count_bound J hc hn x y w xy old xw wy U C Z cu count tip zs nc sat feed gates
  obtain ⟨H,one⟩ := card_eq_one.mp (show (remote J ((univ\C)\Z) y).card=1 by omega)
  exact saturated_pair J hc hn x y w xy old xw wy U C Z H cu count tip zs pair nc sat feed one
    (gates H (one ▸ mem_singleton_self _))

#print axioms gate_count_bound
#print axioms pair_of_at_most_one
end Minimal180.Controlled
