import DescentProof180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def lift (S : Finset V) (p : Bool) : Finset (V ⊕ Unit) :=
  S.disjSum (if p then univ else ∅)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem inl_lift (S : Finset V) (p : Bool) (x : V) : Sum.inl x∈lift S p ↔ x∈S := by
  simp [lift]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem inr_lift (S : Finset V) (p : Bool) (x : Unit) : Sum.inr x∈lift S p ↔ p=true := by
  cases p <;> simp [lift]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem card_lift (S : Finset V) (p : Bool) : (lift S p).card=S.card+p.toNat := by
  cases p <;> simp [lift]

omit [Fintype V] in
theorem eligible_lift (A P : Finset V) (r : V) (a p : Bool) :
    eligible (lift A a) (lift P p) (.inl r)=lift (eligible A P r) (a||p) := by
  classical
  ext v
  rcases v with x|i
  · simp only [eligible_iff,inl_lift]
    rw [show ((Sum.inl x : V ⊕ Unit) ≠ Sum.inl r) ↔ x≠r from not_congr Sum.inl.inj_iff]
  · cases i
    cases a <;> cases p <;> simp [eligible_iff]

theorem present (S : Finset (V ⊕ Unit)) : S=lift (pull Sum.inl S) (decide (Sum.inr ()∈S)) := by
  ext v
  rcases v with x|i
  · simp
  · cases i; simp

theorem erase_cost (U : Finset V) (w : V) :
    weightedLeaves G U ≤ weightedLeaves G (U.erase w)+1 := by
  classical
  have sub : U \ U.erase w ⊆ {w} := by
    intro v h
    obtain ⟨vu,no⟩ := mem_sdiff.mp h
    exact mem_singleton.mpr (Classical.byContradiction (fun ne => no (mem_erase.mpr ⟨ne,vu⟩)))
  have size := card_le_card sub
  rw [card_singleton] at size
  exact (restrict_leaves G U (U.erase w)).trans (Nat.add_le_add_left size _)

theorem attach (hc : G.Connected) (hn : 2<Fintype.card V) (N U : Finset V) (e : Bool) (x : V) (xn : x∈N) :
    weightedLeaves G (U.erase x)+e.toNat ≤ weightedLeaves (ear G N) (lift U e) := by
  cases e
  · simpa only [lift,Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero] using
      attach_lower G (by omega) U N x xn
  · exact gain_at G hc hn N U x xn

theorem rank_mono (N : Finset V) : bipartiteNum G ≤ bipartiteNum (ear G N) := by
  classical
  apply (without_new G N).trans
  apply Finset.sup_le
  intro S h
  exact le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩)

/-- If an unrestricted failed instance has a stable deletion outside the
overlap and the restricted instance is valid, both scores are sharp to one
unit and the entire attachment neighborhood is mandatory downstairs. -/
theorem failed_single (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V) (nz : N.Nonempty)
    (r : V) (odd a p : Bool) (A : Finset V)
    (par : parity (ear G N) (.inl r) odd=lift (parity G r odd) p)
    (single : ¬(a=true ∧ p=true))
    (old : let Q := parity G r odd
           1+A.card+Q.card ≤ weightedLeaves G (eligible A Q r)+bipartiteNum G)
    (bad : let H := ear G N
           let P := parity H (.inl r) odd
           let B := lift A a
           weightedLeaves H (eligible B P (.inl r))+bipartiteNum H < 1+B.card+P.card) :
    let U := eligible A (parity G r odd) r
    let H := ear G N
    let P := parity H (.inl r) odd
    let B := lift A a
    weightedLeaves G U+bipartiteNum G=1+A.card+(parity G r odd).card ∧
      weightedLeaves H (eligible B P (.inl r))+bipartiteNum H=B.card+P.card ∧
      bipartiteNum H=bipartiteNum G ∧
      weightedLeaves H (eligible B P (.inl r))+1=weightedLeaves G U+(a||p).toNat ∧
      ∀ x∈N, x∈U ∧ ∀ T≤G, T.IsTree → (U ∩ leaves T).card=weightedLeaves G U → x∈leaves T := by
  classical
  dsimp only at *
  rw [par,eligible_lift,card_lift,card_lift] at bad ⊢
  let U := eligible A (parity G r odd) r
  let e := a||p
  have mass : a.toNat+p.toNat=e.toNat := by cases a <;> cases p <;> simp_all [e]
  have plus (x) (h : x∈N) := attach G hc hn N U e x h
  obtain ⟨w,wn⟩ := nz
  have gain := plus w wn
  have one := erase_cost G U w
  have rank := rank_mono G N
  change 1+A.card+(parity G r odd).card ≤ weightedLeaves G U+bipartiteNum G at old
  change weightedLeaves (ear G N) (lift U e)+bipartiteNum (ear G N)<1+(A.card+a.toNat)+((parity G r odd).card+p.toNat) at bad
  change weightedLeaves G U+bipartiteNum G=_ ∧ weightedLeaves (ear G N) (lift U e)+_=_ ∧
    _ ∧ weightedLeaves (ear G N) (lift U e)+1=weightedLeaves G U+e.toNat ∧ _
  refine ⟨by omega,by omega,by omega,by omega,fun x xn => (mandatory_iff G hc U x).mp ?_⟩
  have := plus x xn
  omega

omit [Fintype V] in
theorem erase_lift (U : Finset V) (e : Bool) (w : V) :
    (lift U e).erase (.inl w)=lift (U.erase w) e := by
  ext v
  rcases v with x|i
  · simp only [mem_erase,inl_lift]
    rw [show ((Sum.inl x : V ⊕ Unit) ≠ Sum.inl w) ↔ x≠w from not_congr Sum.inl.inj_iff]
  · simp

/-- The two new vertices can use the same old parent. The loss for that
parent is paid just once. All other edges, including a new-new edge, are
arbitrary; old parity stability will only be needed after both deletions. -/
theorem pair_hang (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (M : Finset (V ⊕ Unit)) (w : V) (wn : w∈N) (wm : .inl w∈M) (U : Finset V) (e f : Bool) :
    weightedLeaves G (U.erase w)+e.toNat+f.toNat ≤ weightedLeaves (ear (ear G N) M) (lift (lift U e) f) := by
  have a := attach G hc hn N (U.erase w) e w wn
  rw [erase_idem] at a
  have b := attach (ear G N) (ear_connected G hc _ ⟨w,wn⟩) (by simp only [Fintype.card_sum,Fintype.card_unit]; omega)
    M (lift U e) f (.inl w) wm
  rw [erase_lift] at b
  exact (Nat.add_le_add_right a _).trans b

theorem pair_reduction (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (M : Finset (V ⊕ Unit)) (w : V) (wn : w∈N) (wm : .inl w∈M) (r : V) (odd : Bool)
    (A : Finset V) (a p b q : Bool)
    (stable : parity (ear (ear G N) M) (.inl (.inl r)) odd=lift (lift (parity G r odd) p) q)
    (old : let P := parity G r odd
           1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G)
    (pay : let U := eligible A (parity G r odd) r
           weightedLeaves G U+bipartiteNum G+(a&&p).toNat+(b&&q).toNat ≤
             weightedLeaves G (U.erase w)+bipartiteNum (ear (ear G N) M)) :
    let H := ear (ear G N) M
    let B := lift (lift A a) b
    let P := parity H (.inl (.inl r)) odd
    1+B.card+P.card≤weightedLeaves H (eligible B P (.inl (.inl r)))+bipartiteNum H := by
  dsimp only at *
  rw [stable,eligible_lift,eligible_lift]
  simp only [card_lift]
  have mass (a p : Bool) : a.toNat+p.toNat=(a||p).toNat+(a&&p).toNat := by cases a <;> cases p <;> rfl
  have h1 := mass a p
  have h2 := mass b q
  have := pair_hang G hc hn N M w wn wm (eligible A (parity G r odd) r) (a||p) (b||q)
  omega

#print axioms failed_single
#print axioms pair_hang
#print axioms pair_reduction
end Minimal180
