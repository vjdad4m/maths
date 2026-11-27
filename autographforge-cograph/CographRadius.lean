import Proof137
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order

/-! AutoGraphForge physical rows 143, 818 and 1128. -/

namespace CographRadius
open SimpleGraph Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Cograph (G : SimpleGraph V) := ¬ Graffiti137.InducedPath G 4
def Universal (G : SimpleGraph V) (x : V) := ∀ y, x ≠ y → G.Adj x y

noncomputable def degreesDesc := (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)
noncomputable def slater : ℕ := sInf {k | Fintype.card V ≤ k + ((degreesDesc G).take k).sum}
noncomputable def eccentricity (G : SimpleGraph V) (x : V) := univ.sup (G.dist x)
noncomputable def radius (G : SimpleGraph V) := sInf (Set.range (eccentricity G))
noncomputable def diameter (G : SimpleGraph V) := univ.sup (eccentricity G)
noncomputable def triameter [DecidableEq V] (G : SimpleGraph V) :=
  univ.sup fun a => (univ.erase a).sup fun b =>
    ((univ.erase a).erase b).sup fun c => G.dist a b + G.dist b c + G.dist c a

omit [DecidableRel G.Adj] in
/-- The complement component of any specified vertex gives a join partition. -/
theorem join_at [Nontrivial V] (hc : G.Connected) (hp : Cograph G) (x : V) :
    ∃ (A : V → Prop) (y : V), A x ∧ ¬ A y ∧
      ∀ u v, A u → ¬ A v → G.Adj u v := by
  classical
  have disconnected : ¬ Gᶜ.Connected := fun h => hp (Graffiti137.four_of_connected_complement G hc h)
  have other : ∃ y, ¬ Gᶜ.Reachable x y := by
    by_contra! reach
    exact disconnected ⟨fun a b => (reach a).symm.trans (reach b)⟩
  obtain ⟨y,hy⟩ := other
  refine ⟨Gᶜ.Reachable x, y, .rfl, hy, ?_⟩
  intro u v hu hv
  by_contra missing
  have ne : u ≠ v := by rintro rfl; exact hv hu
  exact hv (hu.trans (((G.compl_adj u v).mpr ⟨ne,missing⟩).reachable))

/-- The original graph is induced on each vertex set, even when the vertex
sets are components of its complement. -/
def componentTests (G J : SimpleGraph V) :=
  ∀ c : J.ConnectedComponent, Cograph (G.induce c.supp)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem component_iff (J : SimpleGraph V) (choice : J = G ∨ J = Gᶜ) :
    Cograph G ↔ componentTests G J := by
  constructor
  · intro no c
    rintro ⟨f,edges⟩
    exact no ⟨f.trans (Function.Embedding.subtype c.supp),edges⟩
  · intro parts
    rintro ⟨f,edges⟩
    let label (i : Fin 4) := J.connectedComponentMk (f i)
    have contained : ∀ i, label i = label 0 := by
      rcases choice with rfl | rfl
      · have step (i j : Fin 4) (h : Graffiti137.Consecutive i j) : label i = label j :=
          ConnectedComponent.connectedComponentMk_eq_of_adj ((edges i j).mpr h)
        have a := step 0 1 (by decide)
        have b := step 1 2 (by decide)
        have c := step 2 3 (by decide)
        intro i
        fin_cases i <;> first | rfl | exact a.symm | exact (a.trans b).symm | exact ((a.trans b).trans c).symm
      · have step (i j : Fin 4) (ne : i ≠ j) (h : ¬ Graffiti137.Consecutive i j) :
            label i = label j := ConnectedComponent.connectedComponentMk_eq_of_adj
          ((G.compl_adj _ _).mpr ⟨fun eqn => ne (f.injective eqn),fun e => h ((edges i j).mp e)⟩)
        have a := step 0 2 (by decide) (by decide)
        have b := step 0 3 (by decide) (by decide)
        have c := step 3 1 (by decide) (by decide)
        intro i
        fin_cases i <;> first | rfl | exact a.symm | exact b.symm | exact (b.trans c).symm
    let inside : Fin 4 ↪ (label 0).supp :=
      ⟨fun i => ⟨f i,contained i⟩,fun _ _ e => f.injective (congrArg Subtype.val e)⟩
    exact parts (label 0) ⟨inside,edges⟩

omit [DecidableRel G.Adj] in
open Classical in
/-- The P4-free predicate satisfies exactly GraphCalc's component recursion. -/
theorem graphCalc_cograph_iff : Cograph G ↔
    (if Fintype.card V ≤ 1 then True else
      if ¬ G.Connected then componentTests G G else
        if ¬ Gᶜ.Connected then componentTests G Gᶜ else False) := by
  split
  · rename_i small
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rintro ⟨f,_⟩
    have := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin] at this
    omega
  · rename_i big
    haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    split
    · exact component_iff G G (Or.inl rfl)
    · rename_i connected
      split
      · exact component_iff G Gᶜ (Or.inr rfl)
      · rename_i coConnected
        exact ⟨fun no => no (Graffiti137.four_of_connected_complement G
          (not_not.mp connected) (not_not.mp coConnected)),False.elim⟩

/-- The first degree is realized by x, and the second bounds every vertex
other than x, including a second vertex tied for maximum. -/
private theorem leaders (hn : 2 ≤ Fintype.card V) :
    ∃ (x : V) (b : ℕ) (l : List ℕ), degreesDesc G = G.degree x :: b :: l ∧
      (∀ y, G.degree y ≤ G.degree x) ∧ (∀ y, y ≠ x → G.degree y ≤ b) := by
  classical
  have len : (degreesDesc G).length = Fintype.card V := by simp [degreesDesc]
  obtain ⟨a,b,l,eqn⟩ : ∃ a b l, degreesDesc G = a :: b :: l := by
    cases hd : degreesDesc G with
    | nil => simp [hd] at len; omega
    | cons a l =>
      cases l with
      | nil => simp [hd] at len; omega
      | cons b l => exact ⟨a,b,l,rfl⟩
  have bag : ((a :: b :: l : List ℕ) : Multiset ℕ) = univ.val.map (G.degree ·) := by
    rw [← eqn, degreesDesc, Multiset.sort_eq]
  have memA : a ∈ univ.val.map (G.degree ·) := by rw [← bag]; simp
  obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp memA
  subst a
  have sorted : (G.degree x :: b :: l).Pairwise (· ≥ ·) := by
    rw [← eqn]
    exact Multiset.sort_sorted _ _
  have maxHead {i : ℕ} {tail : List ℕ} (h : (i :: tail).Pairwise (· ≥ ·)) :
      ∀ k ∈ i :: tail, k ≤ i := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact le_rfl
    · exact (List.pairwise_cons.mp h).1 _ hk
  refine ⟨x,b,l,eqn,?_,?_⟩
  · intro y
    apply maxHead sorted
    change G.degree y ∈ ((G.degree x :: b :: l : List ℕ) : Multiset ℕ)
    rw [bag]
    exact Multiset.mem_map.mpr ⟨y,mem_univ _,rfl⟩
  · intro y hy
    have rest : ((b :: l : List ℕ) : Multiset ℕ) =
        (univ.val.erase x).map (G.degree ·) := by
      apply (Multiset.cons_inj_right (G.degree x)).mp
      rw [← Multiset.map_cons (f := fun z => G.degree z), Multiset.cons_erase (s := univ.val) (mem_univ x)]
      exact bag
    apply maxHead (List.pairwise_cons.mp sorted).2
    change G.degree y ∈ ((b :: l : List ℕ) : Multiset ℕ)
    rw [rest]
    exact Multiset.mem_map.mpr ⟨y,(Multiset.mem_erase_of_ne hy).mpr (mem_univ _),rfl⟩

private theorem universal_iff_degree (x : V) :
    Universal G x ↔ Fintype.card V ≤ 1 + G.degree x := by
  classical
  have sub : G.neighborFinset x ⊆ univ.erase x := by
    intro y hy
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hy).ne.symm,mem_univ _⟩
  have size : (univ.erase x).card + 1 = Fintype.card V := by
    simpa using Finset.card_erase_add_one (mem_univ x)
  constructor
  · intro h
    have rev : univ.erase x ⊆ G.neighborFinset x := fun y hy =>
      (G.mem_neighborFinset _ _).mpr (h y (mem_erase.mp hy).1.symm)
    have bound := card_le_card rev
    rw [G.card_neighborFinset_eq_degree] at bound
    omega
  · intro bound
    have eq := eq_of_subset_of_card_le sub (by rw [G.card_neighborFinset_eq_degree]; omega)
    intro y hxy
    apply (G.mem_neighborFinset _ _).mp
    rw [eq]
    exact mem_erase.mpr ⟨hxy.symm,mem_univ _⟩

private theorem slater_attained :
    Fintype.card V ≤ slater G + ((degreesDesc G).take (slater G)).sum :=
  Nat.sInf_mem (s := {k | Fintype.card V ≤ k + ((degreesDesc G).take k).sum})
    ⟨Fintype.card V, Nat.le_add_right _ _⟩

private theorem slater_pos (hn : 2 ≤ Fintype.card V) : 0 < slater G := by
  have h := slater_attained G
  by_contra! bad
  have hz : slater G = 0 := by omega
  simp [hz] at h
  omega

theorem slater_one_iff (hn : 2 ≤ Fintype.card V) :
    slater G = 1 ↔ ∃ x, Universal G x := by
  obtain ⟨x,b,l,eqn,maximal,_⟩ := leaders G hn
  constructor
  · intro hs
    have h := slater_attained G
    simp [hs,eqn] at h
    exact ⟨x,(universal_iff_degree G x).mpr (by omega)⟩
  · rintro ⟨y,hy⟩
    have bound := (universal_iff_degree G y).mp hy
    have hm := maximal y
    have feasible : Fintype.card V ≤ 1 + ((degreesDesc G).take 1).sum := by
      simp [eqn]; omega
    have hi : slater G ≤ 1 := Nat.sInf_le (s := {k | Fintype.card V ≤ k + ((degreesDesc G).take k).sum}) feasible
    have := slater_pos G hn
    omega

theorem slater_le_two (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (hp : Cograph G) :
    slater G ≤ 2 := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨x,b,l,eqn,_,remaining⟩ := leaders G hn
  obtain ⟨A,y,hx,hy,cross⟩ := join_at G hc hp x
  have distinct : y ≠ x := by rintro rfl; exact hy hx
  have cover : univ ⊆ G.neighborFinset x ∪ G.neighborFinset y := by
    intro z _
    by_cases hz : A z
    · exact mem_union_right _ ((G.mem_neighborFinset _ _).mpr (cross z y hz hy).symm)
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr (cross x z hx hz))
  have size := (card_le_card cover).trans (card_union_le _ _)
  simp only [card_univ, G.card_neighborFinset_eq_degree] at size
  have := remaining y distinct
  apply Nat.sInf_le (s := {k | Fintype.card V ≤ k + ((degreesDesc G).take k).sum})
  change Fintype.card V ≤ 2 + ((degreesDesc G).take 2).sum
  simp [eqn]
  omega

omit [DecidableRel G.Adj] in
theorem dist_le_two (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (hp : Cograph G)
    (x z : V) : G.dist x z ≤ 2 := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨A,y,hx,hy,cross⟩ := join_at G hc hp x
  by_cases hz : A z
  · have first := SimpleGraph.dist_eq_one_iff_adj.mpr (cross x y hx hy)
    have second := SimpleGraph.dist_eq_one_iff_adj.mpr (cross z y hz hy).symm
    have triangle := hc.dist_triangle (u := x) (v := y) (w := z)
    omega
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (cross x z hx hz)]
    decide

omit [DecidableRel G.Adj] in
private theorem radius_pos (hn : 2 ≤ Fintype.card V) (hc : G.Connected) : 0 < radius G := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨x,hx⟩ := Nat.sInf_mem (Set.range_nonempty (eccentricity G))
  obtain ⟨y,hy⟩ := exists_ne x
  have bound : G.dist x y ≤ eccentricity G x := Finset.le_sup (f := G.dist x) (mem_univ y)
  have := hc.pos_dist_of_ne hy.symm
  change eccentricity G x = radius G at hx
  omega

omit [DecidableRel G.Adj] in
theorem radius_one_iff (hn : 2 ≤ Fintype.card V) (hc : G.Connected) :
    radius G = 1 ↔ ∃ x, Universal G x := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  constructor
  · intro one
    obtain ⟨x,hx⟩ := Nat.sInf_mem (Set.range_nonempty (eccentricity G))
    change eccentricity G x = radius G at hx
    refine ⟨x,fun y hy => SimpleGraph.dist_eq_one_iff_adj.mp ?_⟩
    have hle : G.dist x y ≤ eccentricity G x := Finset.le_sup (f := G.dist x) (mem_univ y)
    have := hc.pos_dist_of_ne hy
    omega
  · rintro ⟨x,hx⟩
    have bound : eccentricity G x ≤ 1 := by
      apply Finset.sup_le
      intro y _
      by_cases h : x = y
      · subst y; rw [SimpleGraph.dist_self]; exact Nat.zero_le _
      · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (hx y h)]
    have minBound : radius G ≤ eccentricity G x := Nat.sInf_le (Set.mem_range_self x)
    have := radius_pos G hn hc
    omega

theorem row143 (hn : 2 ≤ Fintype.card V) (hp : Cograph G) (hc : G.Connected) :
    radius G = slater G := by
  obtain ⟨x⟩ := hc.nonempty
  have bound : eccentricity G x ≤ 2 := Finset.sup_le (fun y _ => dist_le_two G hn hc hp x y)
  have minBound : radius G ≤ eccentricity G x := Nat.sInf_le (Set.mem_range_self x)
  have one := (radius_one_iff G hn hc).trans (slater_one_iff G hn).symm
  have := slater_le_two G hn hc hp
  have := slater_pos G hn
  have := radius_pos G hn hc
  omega

/-- Regularity makes every vertex universal if any vertex is universal. -/
private theorem regular_distance (hn : 2 ≤ Fintype.card V) (hp : Cograph G) (hc : G.Connected)
    (hr : ∃ k, G.IsRegularOfDegree k) (x y : V) : G.dist x y ≤ slater G := by
  by_cases one : slater G = 1
  · obtain ⟨u,hu⟩ := (slater_one_iff G hn).mp one
    obtain ⟨k,hk⟩ := hr
    have deg : G.degree x = G.degree u := (hk x).trans (hk u).symm
    have ux := (universal_iff_degree G u).mp hu
    have hx := (universal_iff_degree G x).mpr (deg.symm ▸ ux)
    by_cases eqn : x = y
    · subst y; rw [SimpleGraph.dist_self]; exact Nat.zero_le _
    · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (hx y eqn),one]
  · have := slater_pos G hn
    have := dist_le_two G hn hc hp x y
    omega

theorem row818_connected (hn : 2 ≤ Fintype.card V) (hp : Cograph G)
    (hr : ∃ k, G.IsRegularOfDegree k) (hc : G.Connected) : diameter G ≤ slater G := by
  apply Finset.sup_le
  intro x _
  exact Finset.sup_le (fun y _ => regular_distance G hn hp hc hr x y)

theorem regular_diameter_eq_slater (hn : 2 ≤ Fintype.card V) (hp : Cograph G)
    (hc : G.Connected) (hr : ∃ k, G.IsRegularOfDegree k) : diameter G = slater G := by
  obtain ⟨x⟩ := hc.nonempty
  have minBound : radius G ≤ eccentricity G x := Nat.sInf_le (Set.mem_range_self x)
  have maxBound : eccentricity G x ≤ diameter G := Finset.le_sup (f := eccentricity G) (mem_univ x)
  apply le_antisymm (row818_connected G hn hp hr hc)
  rw [← row143 G hn hp hc]
  exact minBound.trans maxBound

omit [DecidableRel G.Adj] in
theorem triameter_le_three_diameter [DecidableEq V] : triameter G ≤ 3 * diameter G := by
  have bound (x y : V) : G.dist x y ≤ diameter G := calc
    G.dist x y ≤ eccentricity G x := Finset.le_sup (f := G.dist x) (mem_univ y)
    _ ≤ diameter G := Finset.le_sup (f := eccentricity G) (mem_univ x)
  simp only [triameter, Finset.sup_le_iff]
  intro x _ y _ z _
  have := bound x y
  have := bound y z
  have := bound z x
  omega

theorem row1128_connected [DecidableEq V] (hn : 2 ≤ Fintype.card V) (hp : Cograph G)
    (hr : ∃ k, G.IsRegularOfDegree k) (hc : G.Connected) : triameter G ≤ 3 * slater G :=
  (triameter_le_three_diameter G).trans (Nat.mul_le_mul_left 3 (row818_connected G hn hp hr hc))

/-- GraphCalc's numeric distance values are defined only on connected
nontrivial inputs. Its triameter over an empty set of triples starts at zero. -/
noncomputable def onConnected {α : Type*} (G : SimpleGraph V) (v : α) : Option α := by
  classical
  exact if G.Connected then some v else none

theorem row818 (hn : 2 ≤ Fintype.card V) (hp : Cograph G) (hr : ∃ k, G.IsRegularOfDegree k)
    {d : ℕ} (hd : onConnected G (diameter G) = some d) : d ≤ slater G := by
  classical
  unfold onConnected at hd
  split at hd
  · rename_i hc
    cases hd
    exact row818_connected G hn hp hr hc
  · contradiction

theorem row1128 [DecidableEq V] (hn : 2 ≤ Fintype.card V) (hp : Cograph G)
    (hr : ∃ k, G.IsRegularOfDegree k) {t : ℕ} (ht : onConnected G (triameter G) = some t) :
    t ≤ 3 * slater G := by
  classical
  unfold onConnected at ht
  split at ht
  · rename_i hc
    cases ht
    exact row1128_connected G hn hp hr hc
  · contradiction

/-- AutoGraphForge's separate diameter wrapper uses positive infinity as
the disconnected sentinel. -/
noncomputable def sourceDiameter (G : SimpleGraph V) : WithTop ℚ := by
  classical
  exact if G.Connected then ((diameter G : ℚ) : WithTop ℚ) else ⊤

theorem row818_infinity_counterexample :
    let H : SimpleGraph (Fin 2) := ⊥
    2 ≤ Fintype.card (Fin 2) ∧ Cograph H ∧ (∃ k, H.IsRegularOfDegree k) ∧
      ¬ sourceDiameter H ≤ ((slater H : ℚ) : WithTop ℚ) := by
  dsimp only
  refine ⟨by decide, ?_, ⟨0,fun v => SimpleGraph.bot_degree v⟩, ?_⟩
  · rintro ⟨f,h⟩
    exact ((h 0 1).mpr (by decide) : (⊥ : SimpleGraph (Fin 2)).Adj (f 0) (f 1))
  · rw [sourceDiameter, if_neg SimpleGraph.bot_not_connected]
    exact WithTop.not_top_le_coe _

#print axioms graphCalc_cograph_iff
#print axioms join_at
#print axioms slater_one_iff
#print axioms row143
#print axioms regular_diameter_eq_slater
#print axioms row818
#print axioms row1128
#print axioms row818_infinity_counterexample

end CographRadius
