import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Graffiti384b
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A pair of adjacent neighbors is exactly the pair of other vertices of an incident triangle. -/
def trianglesAt (v : V) : ℕ :=
  (((G.neighborFinset v).powersetCard 2).filter
    (fun p => ∀ x ∈ p, ∀ y ∈ p, x ≠ y → G.Adj x y)).card

def types : Finset ℕ := univ.image (trianglesAt G)

def nbr (v : V) (s : Finset V) := (s.filter (G.Adj v)).card

def TwoDominates (d : Finset V) : Prop := ∀ v ∉ d, 2 ≤ nbr G v d

noncomputable def gamma : ℕ := sInf {k : ℕ | ∃ d, TwoDominates G d ∧ d.card = k}

def high : Finset V := univ.filter (fun v => 3 ≤ G.degree v)

/-- Since |T| ≤ n, this natural-number expression equals the catalogue floor. -/
def bound := Fintype.card V - ((types G).card + 1) / 2

private def cut (a b : Finset V) : ℕ := ∑ x ∈ a, ∑ y ∈ b, if G.Adj x y then 1 else 0

omit [Fintype V] [DecidableEq V] in
private theorem cut_symm (a b : Finset V) : cut G a b = cut G b a := by
  unfold cut
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  by_cases h : G.Adj x y
  · simp [h, G.symm h]
  · have hn : ¬G.Adj y x := fun h' => h (G.symm h')
    simp [h, hn]

omit [Fintype V] in
private theorem cut_insert {v : V} {a : Finset V} (hv : v ∉ a) (b : Finset V) :
    cut G (insert v a) b = nbr G v b + cut G a b := by
  simp [cut, nbr, hv]

private theorem nbr_partition (v : V) (a : Finset V) :
    nbr G v a + nbr G v aᶜ = G.degree v := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset v)
    (fun x => x ∈ a)
  have h₁ : (G.neighborFinset v).filter (fun x => x ∈ a) = a.filter (G.Adj v) := by
    ext x
    simp [and_comm]
  have h₂ : (G.neighborFinset v).filter (fun x => x ∉ a) = aᶜ.filter (G.Adj v) := by
    ext x
    simp [and_comm]
  simpa only [h₁, h₂, card_neighborFinset_eq_degree, nbr] using h

private theorem maximal_side {a : Finset V}
    (hm : ∀ s, cut G s sᶜ ≤ cut G a aᶜ) {v : V} (hv : v ∈ a) :
    nbr G v a ≤ nbr G v aᶜ := by
  have h := hm (a.erase v)
  rw [compl_erase, cut_symm G (a.erase v), cut_insert G (by simpa using hv),
    cut_symm G aᶜ (a.erase v)] at h
  have e := cut_insert G (not_mem_erase v a) aᶜ
  rw [insert_erase hv] at e
  have f : nbr G v (a.erase v) = nbr G v a := by
    unfold nbr
    congr 1
    ext x
    by_cases hx : x = v
    · subst x
      simp
    · simp [hx]
  omega

private theorem gamma_le_of_side {a : Finset V}
    (hm : ∀ s, cut G s sᶜ ≤ cut G a aᶜ) :
    gamma G ≤ Fintype.card V - ((high G).filter (fun v => v ∈ a)).card := by
  let o := (high G).filter (fun v => v ∈ a)
  have hd : TwoDominates G oᶜ := by
    intro v hv
    have hvo : v ∈ o := by simpa using hv
    obtain ⟨hh, ha⟩ := mem_filter.mp hvo
    have hdeg : 3 ≤ G.degree v := (mem_filter.mp hh).2
    have h₁ := maximal_side G hm ha
    have h₂ := nbr_partition G v a
    have hsub : aᶜ.filter (G.Adj v) ⊆ oᶜ.filter (G.Adj v) := by
      intro x hx
      obtain ⟨hm', hadj⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_compl.mpr (fun hxo => mem_compl.mp hm' (mem_filter.mp hxo).2), hadj⟩
    have h₃ : nbr G v aᶜ ≤ nbr G v oᶜ := card_le_card hsub
    omega
  have h : gamma G ≤ oᶜ.card := Nat.sInf_le ⟨oᶜ, hd, rfl⟩
  simpa [o, card_compl] using h

/-- A maximum cut supplies two outside neighbors to each degree-at-least-three vertex. -/
theorem high_bound : gamma G ≤ Fintype.card V - ((high G).card + 1) / 2 := by
  obtain ⟨a, _, h⟩ := exists_max_image (univ : Finset (Finset V)) (fun a => cut G a aᶜ)
    univ_nonempty
  have h₁ s := h s (mem_univ s)
  have h₂ : ∀ s, cut G s sᶜ ≤ cut G aᶜ aᶜᶜ := by
    intro s
    simpa only [compl_compl, cut_symm G aᶜ a] using h₁ s
  have h₃ := gamma_le_of_side G h₁
  have h₄ := gamma_le_of_side G h₂
  simp only [mem_compl] at h₄
  have h₅ := filter_card_add_filter_neg_card_eq_card (s := high G) (fun v => v ∈ a)
  omega

theorem type_bound : (types G).card ≤ (high G).card + 2 := by
  have sub : types G ⊆ (high G).image (trianglesAt G) ∪ {0, 1} := by
    intro t ht
    obtain ⟨v, _, rfl⟩ := mem_image.mp ht
    by_cases hv : 3 ≤ G.degree v
    · exact mem_union_left _ (mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩, rfl⟩)
    · have h := card_filter_le ((G.neighborFinset v).powersetCard 2)
          (fun p => ∀ x ∈ p, ∀ y ∈ p, x ≠ y → G.Adj x y)
      rw [card_powersetCard, card_neighborFinset_eq_degree] at h
      change trianglesAt G v ≤ _ at h
      have hc : (G.degree v).choose 2 ≤ 1 := by
        have hd : G.degree v = 0 ∨ G.degree v = 1 ∨ G.degree v = 2 := by omega
        rcases hd with h' | h' | h' <;> rw [h'] <;> decide
      apply mem_union_right
      simp only [mem_insert, mem_singleton]
      omega
  have hu := card_union_le ((high G).image (trianglesAt G)) ({0, 1} : Finset ℕ)
  have hp : ({0, 1} : Finset ℕ).card = 2 := by decide
  have hi := card_image_le (s := high G) (f := trianglesAt G)
  have hs := card_le_card sub
  omega

theorem within_one : gamma G ≤ bound G + 1 := by
  have h := high_bound G
  have t := type_bound G
  unfold bound
  omega

theorem exact_of_high (h : ((types G).card + 1) / 2 ≤ ((high G).card + 1) / 2) :
    gamma G ≤ bound G := by
  exact (high_bound G).trans (Nat.sub_le_sub_left h _)

private theorem gamma_le_omit (o : Finset V) (h : ∀ v ∈ o, 2 ≤ nbr G v oᶜ) :
    gamma G ≤ Fintype.card V - o.card := by
  have hd : TwoDominates G oᶜ := fun v hv => h v (by simpa using hv)
  simpa only [card_compl] using (Nat.sInf_le (s := {k : ℕ | ∃ d, TwoDominates G d ∧ d.card = k})
    (m := oᶜ.card) ⟨oᶜ, hd, rfl⟩)

private theorem omit_one (hc : G.Connected) (hn : 2 < Fintype.card V) :
    gamma G ≤ Fintype.card V - 1 := by
  have hex : ∃ v, 2 ≤ G.degree v := by
    by_contra! h
    obtain ⟨r⟩ := hc.nonempty
    let s := insert r (G.neighborFinset r)
    have cover : univ ⊆ s := by
      intro y hy
      clear hy
      have reach := (G.reachable_iff_reflTransGen r y).mp (hc.preconnected r y)
      induction reach with
      | refl => exact mem_insert_self _ _
      | tail _ hadj ih =>
        rcases mem_insert.mp ih with he | ha
        · rw [he] at hadj
          exact mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr hadj)
        · have hr := G.symm ((G.mem_neighborFinset _ _).mp ha)
          have eq := (card_le_one (s := G.neighborFinset _)).mp (Nat.le_of_lt_succ (h _))
            _ ((G.mem_neighborFinset _ _).mpr hr) _ ((G.mem_neighborFinset _ _).mpr hadj)
          exact mem_insert.mpr (Or.inl eq.symm)
    have hs := card_le_card cover
    have hh := card_insert_le r (G.neighborFinset r)
    simp only [card_univ] at hs
    have hr := h r
    change (G.neighborFinset r).card < 2 at hr
    change Fintype.card V ≤ (insert r (G.neighborFinset r)).card at hs
    omega
  obtain ⟨v, hv⟩ := hex
  have h := gamma_le_omit G {v} (by
    intro w hw
    have hwv := mem_singleton.mp hw
    subst w
    have e : ({v} : Finset V)ᶜ.filter (G.Adj v) = G.neighborFinset v := by
      ext x
      by_cases hx : x = v
      · subst x
        simp
      · simp [hx]
    simpa [nbr, e] using hv)
  simpa using h

private theorem omit_two_of_triangles {v : V} (hv : 2 ≤ trianglesAt G v) :
    gamma G ≤ Fintype.card V - 2 := by
  let links := ((G.neighborFinset v).powersetCard 2).filter
    (fun p => ∀ x ∈ p, ∀ y ∈ p, x ≠ y → G.Adj x y)
  change 2 ≤ links.card at hv
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < links.card by omega)
  obtain ⟨q, hq, hne⟩ := exists_ne_of_one_lt_card hv p
  have pair_info (a : Finset V) (ha : a ∈ links) :=
    mem_powersetCard.mp (mem_filter.mp ha).1
  obtain ⟨_, hp₂⟩ := pair_info p hp
  obtain ⟨_, hq₂⟩ := pair_info q hq
  have hxsub : ¬p ⊆ q := fun H => hne (eq_of_subset_of_card_le H (by omega)).symm
  have hysub : ¬q ⊆ p := fun H => hne (eq_of_subset_of_card_le H (by omega))
  obtain ⟨x, hx, hx'⟩ := not_subset.mp hxsub
  obtain ⟨y, hy, hy'⟩ := not_subset.mp hysub
  have xy : x ≠ y := fun e => hx' (e ▸ hy)
  let o : Finset V := {x, y}
  have good {a : Finset V} (ha : a ∈ links) {w z : V} (hw : w ∈ a) (hz : z ∉ a)
      (ho : o = {w,z}) : 2 ≤ nbr G w oᶜ := by
    obtain ⟨haN, ha₂⟩ := pair_info a ha
    obtain ⟨u, hu, huw⟩ := exists_ne_of_one_lt_card (by omega : 1 < a.card) w
    have hwu := (mem_filter.mp ha).2 w hw u hu huw.symm
    have hvw := (G.mem_neighborFinset _ _).mp (haN hw)
    have hvu := (G.mem_neighborFinset _ _).mp (haN hu)
    have hvz : v ≠ z := by
      intro e
      subst z
      have hvo : v ∈ o := by simp [ho]
      have hnot : v ∉ o := by
        have h₁ := (G.mem_neighborFinset _ _).mp ((pair_info p hp).1 hx)
        have h₂ := (G.mem_neighborFinset _ _).mp ((pair_info q hq).1 hy)
        simp [o, h₁.ne, h₂.ne]
      exact hnot hvo
    have huz : u ≠ z := fun e => hz (e ▸ hu)
    have hh : ({v,u} : Finset V) ⊆ oᶜ.filter (G.Adj w) := by
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simp [ho, hvw.ne, hvz, hvw.symm]
      · obtain rfl := mem_singleton.mp hi
        simp [ho, huw, huz, hwu]
    have hcard := card_le_card hh
    simpa [nbr, hvu.ne] using hcard
  have h := gamma_le_omit G o (by
    intro w hw
    rcases mem_insert.mp hw with rfl | h
    · exact good hp hx hy' rfl
    · obtain rfl := mem_singleton.mp h
      exact good hq hy hx' (Finset.pair_comm _ _))
  simpa [o, xy] using h

theorem exact_of_at_most_four (hc : G.Connected) (hn : 2 < Fintype.card V)
    (ht : (types G).card ≤ 4) : gamma G ≤ bound G := by
  by_cases h : (types G).card ≤ 2
  · have h₁ := omit_one G hc hn
    unfold bound
    omega
  · have he : ∃ v, 2 ≤ trianglesAt G v := by
      by_contra! hsmall
      have sub : types G ⊆ {0, 1} := by
        rintro t ht'
        obtain ⟨v, _, rfl⟩ := mem_image.mp ht'
        simp only [mem_insert, mem_singleton]
        have := hsmall v
        omega
      have hh := card_le_card sub
      have hh₂ : ({0,1} : Finset ℕ).card = 2 := by decide
      omega
    obtain ⟨v, hv⟩ := he
    have h₂ := omit_two_of_triangles G hv
    unfold bound
    omega

def nonleaves : Finset V := univ.filter (fun v => 2 ≤ G.degree v)

private def monoEdges (c : V → Fin 3) : Finset (V × V) :=
  univ.filter (fun e => G.Adj e.1 e.2 ∧ c e.1 = c e.2)

/-- In a three-coloring minimizing monochromatic edges, every nonleaf sees two
neighbors outside its own color. A violation would leave a neighbor color unused. -/
theorem nonleaf_bound : gamma G ≤ Fintype.card V - ((nonleaves G).card + 2) / 3 := by
  classical
  obtain ⟨c, _, hmin⟩ := exists_min_image (univ : Finset (V → Fin 3))
    (fun f => (monoEdges G f).card) univ_nonempty
  have localGood (v : V) (hv : v ∈ nonleaves G) :
      2 ≤ ((G.neighborFinset v).filter (fun u => c u ≠ c v)).card := by
    by_contra! hbad
    let b := (G.neighborFinset v).filter (fun u => c u ≠ c v)
    have small : b.card ≤ 1 := Nat.le_of_lt_succ hbad
    have hc := card_insert_le (c v) (b.image c)
    have hi := card_image_le (s := b) (f := c)
    obtain ⟨j, _, hj⟩ := exists_mem_not_mem_of_card_lt_card
      (s := insert (c v) (b.image c)) (t := univ) (by simp only [card_univ, Fintype.card_fin]; omega)
    have unused {x : V} (hx : G.Adj v x) : c x ≠ j := by
      intro e
      apply hj
      by_cases hh : c x = c v
      · exact mem_insert.mpr (Or.inl (e.symm.trans hh))
      · exact mem_insert_of_mem (mem_image.mpr ⟨x, mem_filter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hx, hh⟩, e⟩)
    let f := Function.update c v j
    have changed {x y : V} (hxy : G.Adj x y) (he : f x = f y) :
        x ≠ v ∧ y ≠ v := by
      constructor
      · rintro rfl
        have hh : y ≠ x := hxy.ne.symm
        have hjy := unused hxy
        simp [f, hh] at he
        exact hjy he.symm
      · rintro rfl
        have hh : x ≠ y := hxy.ne
        have hjx := unused hxy.symm
        simp [f, hh] at he
        exact hjx he
    have sub : monoEdges G f ⊆ monoEdges G c := by
      rintro ⟨x,y⟩ h
      obtain ⟨ha, he⟩ := (mem_filter.mp h).2
      obtain ⟨hx, hy⟩ := changed ha he
      exact mem_filter.mpr ⟨mem_univ _, ha, by simpa [f, hx, hy] using he⟩
    have hv₂ := (mem_filter.mp hv).2
    obtain ⟨w, hw, hw'⟩ := exists_mem_not_mem_of_card_lt_card (s := b) (t := G.neighborFinset v)
      (by rw [card_neighborFinset_eq_degree]; omega)
    have ha := (G.mem_neighborFinset _ _).mp hw
    have he : c w = c v := by
      exact Classical.byContradiction (fun hh => hw' (mem_filter.mpr ⟨hw, hh⟩))
    have strict := (ssubset_iff_of_subset sub).mpr
      (show ∃ e ∈ monoEdges G c, e ∉ monoEdges G f from
        ⟨(v,w), mem_filter.mpr ⟨mem_univ _, ha, he.symm⟩,
          fun h => (changed ha (mem_filter.mp h).2.2).1 rfl⟩)
    exact (Nat.not_lt_of_le (hmin f (mem_univ f))) (card_lt_card strict)
  let bucket (j : Fin 3) := (nonleaves G).filter (fun v => c v = j)
  obtain ⟨j, _, hj⟩ := exists_max_image (univ : Finset (Fin 3)) (fun i => (bucket i).card)
    univ_nonempty
  have hsum : (nonleaves G).card = ∑ i : Fin 3, (bucket i).card :=
    card_eq_sum_card_fiberwise (f := c) (fun _ _ => mem_univ _)
  have hbig : (nonleaves G).card ≤ 3 * (bucket j).card := by
    rw [hsum]
    calc
      _ ≤ ∑ _i : Fin 3, (bucket j).card := sum_le_sum hj
      _ = _ := by simp
  have h := gamma_le_omit G (bucket j) (by
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := mem_filter.mp hv
    apply (localGood v hv₁).trans
    apply card_le_card
    intro w hw
    obtain ⟨ha, hne⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨mem_compl.mpr (fun h => hne ((mem_filter.mp h).2.trans hv₂.symm)),
      (G.mem_neighborFinset _ _).mp ha⟩)
  omega

end Graffiti384b

#print axioms Graffiti384b.within_one
#print axioms Graffiti384b.exact_of_high
#print axioms Graffiti384b.exact_of_at_most_four
#print axioms Graffiti384b.nonleaf_bound
