import OuterCoreBounds133
import FirstBandFour133

namespace Graffiti133OuterCore
open SimpleGraph Graffiti133 Graffiti133Camby Graffiti133Revisit Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

noncomputable def nbr (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

theorem mem_nbr {G : SimpleGraph V} {v w : V} : w∈nbr G v ↔ G.Adj v w := by
  classical
  simp [nbr]

noncomputable def walkReach (G : SimpleGraph V) : Nat → V → Finset V
  | 0, v => by classical exact {v}
  | n+1, v => by
    classical
    exact (nbr G v).biUnion (walkReach G n)

theorem mem_walkReach {G : SimpleGraph V} {v w : V} (p : G.Walk v w) :
    w∈walkReach G p.length v := by
  classical
  induction p with
  | nil => simp [walkReach]
  | @cons u v w hv p ih =>
    change w∈(nbr G u).biUnion (walkReach G p.length)
    exact Finset.mem_biUnion.mpr ⟨v,mem_nbr.mpr hv,ih⟩

theorem walkReach_card_le (G : SimpleGraph V) (d : Nat)
    (cap : ∀ v,(nbr G v).card≤d) (n : Nat) (v : V) :
    (walkReach G n v).card≤d^n := by
  classical
  induction n generalizing v with
  | zero => simp [walkReach]
  | succ n ih =>
    change ((nbr G v).biUnion (walkReach G n)).card≤d^(n+1)
    calc
      _ ≤ ∑ w∈nbr G v,(walkReach G n w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w∈nbr G v,d^n := Finset.sum_le_sum (fun w _ => ih w)
      _ = (nbr G v).card*d^n := by simp
      _ ≤ d^(n+1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ (cap v)

theorem order_le_sum_deg_pow_of_diameter (G : SimpleGraph V) (hc : G.Connected)
    (d b : Nat) (degree : ∀ v, (nbr G v).card≤d)
    (diam : ∀ x y,G.dist x y≤b) :
    Fintype.card V ≤ ∑ k∈Finset.range (b+1),d^k := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  let S := (Finset.range (b+1)).biUnion (fun n => walkReach G n v)
  have e : S=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v w
    exact Finset.mem_biUnion.mpr ⟨p.length,Finset.mem_range.mpr (by have h := diam v w; omega),mem_walkReach p⟩
  calc
    Fintype.card V = S.card := by rw [e,Finset.card_univ]
    _ ≤ ∑ n∈Finset.range (b+1),(walkReach G n v).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun n _ => walkReach_card_le G d degree n v)

theorem connected_exterior_order (G : SimpleGraph V) (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (C E : Finset V) (dom : ∀ x∉C, ∃ y∈C,G.Adj x y)
    (sep : Disjoint C E) (hc : (G.induce (E : Set V)).Connected) :
    E.card ≤ ∑ k∈Finset.range 8,C.card^k := by
  classical
  let J := G.induce (E : Set V)
  have out (x : (E : Set V)) : x.val∉C :=
    fun a => (Finset.disjoint_left.mp sep a x.property)
  have nJ : NoPath J 9 := by
    rintro ⟨f,hf⟩
    exact h9 ⟨Subtype.val ∘ f,Subtype.val_injective.comp hf.1,hf.2⟩
  have degree (x : (E : Set V)) : (nbr J x).card≤C.card := by
    apply le_trans _ (external_degree_le_core h4 C dom x.val (out x))
    apply Finset.card_le_card_of_injOn (fun y => y.val)
    · intro y hy
      have h : J.Adj x y := mem_nbr.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,out y,h⟩
    · exact Subtype.val_injective.injOn
  have diam (x y : (E : Set V)) : J.dist x y≤7 := by
    by_cases h : J.dist x y≤7
    · exact h
    exfalso
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
    change p.length = J.dist x y at hp
    obtain ⟨f,hf,ha⟩ := geodesic_induced hc p hp
    exact nJ (trim_path (by omega) ⟨hf,ha⟩)
  have outBound := order_le_sum_deg_pow_of_diameter J hc C.card 7 degree diam
  have ec : Fintype.card (E : Set V) = E.card := by exact Fintype.card_coe E
  rwa [ec] at outBound

theorem core_nine_connected_exterior_order (G : SimpleGraph V) (h4 : FourCycleFree G)
    (h9 : NoPath G 9) (C E : Finset V) (small : C.card≤9)
    (dom : ∀ x∉C, ∃ y∈C,G.Adj x y) (sep : Disjoint C E) (hc : (G.induce (E : Set V)).Connected) :
    E.card ≤ 5380840 := by
  calc E.card ≤ ∑ k∈Finset.range 8,C.card^k := connected_exterior_order G h4 h9 C E dom sep hc
    _ ≤ ∑ k∈Finset.range 8,9^k := Finset.sum_le_sum (fun k _ => Nat.pow_le_pow_left small k)
    _ = 5380840 := by decide

#print axioms connected_exterior_order
#print axioms core_nine_connected_exterior_order
end Graffiti133OuterCore
