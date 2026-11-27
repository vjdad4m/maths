import TreeBudget

namespace Graffiti199Depleted.Catalogue.IndependenceObstruction

open SimpleGraph

abbrev Hub (m : ℕ) := (Fin 3 × Fin 3) ⊕ Fin m
abbrev Vertices (m : ℕ) := (Fin 3 ⊕ Fin 3) ⊕ Hub m

def group {m : ℕ} : Hub m → Fin 3
  | .inl (i, _) => i
  | .inr _ => 0

def adj {m : ℕ} : Vertices m → Vertices m → Prop
  | .inl _, .inl _ => False
  | .inl (.inl _), .inr _ => True
  | .inr _, .inl (.inl _) => True
  | .inl (.inr i), .inr h => group h = i
  | .inr h, .inl (.inr i) => group h = i
  | .inr h, .inr k => h ≠ k

/-- Nine hubs in a clique, three common independent leaves, and one
private independent leaf for each group of three hubs.
Extra hubs may join group zero. -/
def graph (m : ℕ) : SimpleGraph (Vertices m) where
  Adj := adj
  symm := by
    rintro (a|a) (b|b) h
    · cases a <;> cases b <;> exact h
    · cases a <;> exact h
    · cases b <;> exact h
    · exact h.symm
  loopless := by
    rintro (a|a)
    · cases a <;> exact id
    · exact fun h => h rfl

variable {m : ℕ}

private abbrev Survives (D : Finset (Vertices m)) := {v : Vertices m // v ∉ D}

private def hubAt (i : Fin 3) : Fin 3 ↪ Vertices m :=
  ⟨fun j => .inr (.inl (i,j)), fun _ _ h => (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))).2⟩

private def hubsOf (i : Fin 3) : Finset (Vertices m) := Finset.univ.map (hubAt i)

private theorem exists_surviving_hub (D : Finset (Vertices m)) (small : D.card < 3) (i : Fin 3) :
    ∃ h : Hub m, group h = i ∧ (Sum.inr h : Vertices m) ∉ D := by
  have card : (hubsOf (m := m) i).card = 3 := by simp [hubsOf]
  obtain ⟨v,hv,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show D.card < (hubsOf (m := m) i).card by omega)
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hv
  exact ⟨.inl (i,k),rfl,off⟩

theorem connectivity_at_least_three (m : ℕ) : ConnectivityAtLeast (graph m) 3 := by
  have size : 3 < Fintype.card (Vertices m) := by
    simp
    omega
  refine ⟨size,?_⟩
  intro D small
  let H := (graph m).induce ((↑D : Set (Vertices m))ᶜ)
  obtain ⟨hub,_,alive⟩ := exists_surviving_hub D small 0
  let anchor : Survives D := ⟨.inr hub,alive⟩
  have reachHub (h : Hub m) (stay : (Sum.inr h : Vertices m) ∉ D) :
      H.Reachable ⟨.inr h,stay⟩ anchor := by
    by_cases eq : h = hub
    · subst h
      exact .rfl
    · exact (show H.Adj ⟨.inr h,stay⟩ anchor from eq).reachable
  have reach (v : Survives D) : H.Reachable v anchor := by
    rcases v with ⟨(c|p)|h,keep⟩
    · exact (show H.Adj ⟨.inl (.inl c),keep⟩ anchor from trivial).reachable
    · obtain ⟨h,his,ok⟩ := exists_surviving_hub D small p
      exact (show H.Adj ⟨.inl (.inr p),keep⟩ ⟨.inr h,ok⟩ from his).reachable.trans (reachHub h ok)
    · exact reachHub h keep
  exact @SimpleGraph.Connected.mk _ H (fun x y => (reach x).trans (reach y).symm) ⟨anchor⟩

private theorem surviving_hubs_one (h : Hub m) (hg : group h = 1) :
    (Sum.inr h : Vertices m) ∈ hubsOf 1 := by
  rcases h with ⟨i,j⟩|k
  · change i = 1 at hg
    subst i
    exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  · exact (by decide : (0 : Fin 3) ≠ 1) hg |>.elim

theorem exact_connectivity (m : ℕ) : vertexConnectivity (graph m) = 3 := by
  classical
  apply Nat.le_antisymm
  · by_contra! tooLarge
    have all := connectivityAtLeast_vertexConnectivity (G := graph m)
    let D : Finset (Vertices m) := hubsOf 1
    have card : D.card = 3 := by simp [D,hubsOf]
    have notLeaf (l : Fin 3 ⊕ Fin 3) : (Sum.inl l : Vertices m) ∉ D := by
      intro h
      obtain ⟨j,_,eq⟩ := Finset.mem_map.mp h
      cases eq
    let a : Survives D := ⟨.inl (.inr 1),notLeaf _⟩
    let b : Survives D := ⟨.inl (.inl 0),notLeaf _⟩
    have iso (v : Survives D) :
        ¬ ((graph m).induce ((↑D : Set (Vertices m))ᶜ)).Adj a v := by
      rcases v with ⟨l|h,stay⟩
      · exact id
      · exact fun e => stay (surviving_hubs_one h e)
    have different : a ≠ b := fun e => by cases congrArg Subtype.val e
    have conn := all.2 D (by omega)
    obtain ⟨walk⟩ := conn.preconnected a b
    have equal {v : Survives D}
        (w : ((graph m).induce ((↑D : Set (Vertices m))ᶜ)).Walk a v) : a = v := by
      cases w with
      | nil => rfl
      | cons e _ => exact (iso _ e).elim
    exact different (equal walk)
  · unfold vertexConnectivity
    exact Finset.le_sup (f := id)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (connectivity_at_least_three m).1,
        connectivity_at_least_three m⟩)

private theorem no_triangle_in_tree {X : Type*} {H : SimpleGraph X} (tree : H.IsTree)
    {a b c : X} (ab : H.Adj a b) (ac : H.Adj a c) (bc : H.Adj b c) : False := by
  have unique := (SimpleGraph.isTree_iff_existsUnique_path.mp tree).2 a b
  let p := ab.toWalk
  let q := SimpleGraph.Walk.cons ac bc.symm.toWalk
  have pathP : p.IsPath := by simp [p,SimpleGraph.Adj.toWalk,SimpleGraph.Walk.isPath_def,ab.ne]
  have pathQ : q.IsPath := by
    simp [q,SimpleGraph.Adj.toWalk,SimpleGraph.Walk.isPath_def,ab.ne,ac.ne,bc.ne.symm]
  have len := congrArg SimpleGraph.Walk.length (unique.unique pathP pathQ)
  exact (by decide : (1 : ℕ) ≠ 2) len

private def privateLeaves (m : ℕ) : Finset (Vertices m) :=
  Finset.univ.map (⟨fun i : Fin 3 => .inl (.inr i),
    fun _ _ h => Sum.inr.inj (Sum.inl.inj h)⟩ : Fin 3 ↪ Vertices m)

private def commonLeaves (m : ℕ) : Finset (Vertices m) :=
  Finset.univ.map (⟨fun i : Fin 3 => .inl (.inl i),
    fun _ _ h => Sum.inl.inj (Sum.inl.inj h)⟩ : Fin 3 ↪ Vertices m)

private theorem isTree_card_bound (S : Finset (Vertices m))
    (tree : ((graph m).induce (↑S : Set (Vertices m))).IsTree) : S.card ≤ 5 := by
  classical
  let H := (graph m).induce (↑S : Set (Vertices m))
  let hubs := S.filter fun v => ∃ h : Hub m, Sum.inr h = v
  have hm (v : Vertices m) : v ∈ hubs ↔ v ∈ S ∧ ∃ h : Hub m, Sum.inr h = v := by simp [hubs]
  have atMost : hubs.card ≤ 2 := by
    by_contra! many
    obtain ⟨a,ma,b,mb,c,mc,ab,ac,bc⟩ := Finset.two_lt_card.mp many
    obtain ⟨ma',ha,rfl⟩ := (hm a).mp ma
    obtain ⟨mb',hb,rfl⟩ := (hm b).mp mb
    obtain ⟨mc',hc,rfl⟩ := (hm c).mp mc
    exact no_triangle_in_tree tree
      (show H.Adj ⟨.inr ha,ma'⟩ ⟨.inr hb,mb'⟩ from fun eq => ab (congrArg Sum.inr eq))
      (show H.Adj ⟨.inr ha,ma'⟩ ⟨.inr hc,mc'⟩ from fun eq => ac (congrArg Sum.inr eq))
      (show H.Adj ⟨.inr hb,mb'⟩ ⟨.inr hc,mc'⟩ from fun eq => bc (congrArg Sum.inr eq))
  have neighbor_in_tree {u v : Vertices m} (hu : u ∈ S) (hv : v ∈ S) (ne : u ≠ v) :
      ∃ w ∈ S, (graph m).Adj u w := by
    obtain ⟨p⟩ := tree.1.preconnected ⟨u,hu⟩ ⟨v,hv⟩
    cases p with
    | nil => exact (ne rfl).elim
    | @cons a b c e _ => exact ⟨b.val,b.property,e⟩
  by_cases many : 1 < hubs.card
  · obtain ⟨a,ma,b,mb,ab⟩ := Finset.one_lt_card.mp many
    obtain ⟨ma',ha,rfl⟩ := (hm a).mp ma
    obtain ⟨mb',hb,rfl⟩ := (hm b).mp mb
    have sub : S ⊆ hubs ∪ privateLeaves m := by
      rintro ((i|i)|h) mem
      · exact (no_triangle_in_tree tree
          (show H.Adj ⟨.inr ha,ma'⟩ ⟨.inr hb,mb'⟩ from fun eq => ab (congrArg Sum.inr eq))
          (show H.Adj ⟨.inr ha,ma'⟩ ⟨.inl (.inl i),mem⟩ from trivial)
          (show H.Adj ⟨.inr hb,mb'⟩ ⟨.inl (.inl i),mem⟩ from trivial)).elim
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩))
      · exact Finset.mem_union.mpr (Or.inl ((hm _).mpr ⟨mem,h,rfl⟩))
    have count := (Finset.card_le_card sub).trans (Finset.card_union_le hubs (privateLeaves m))
    have pc : (privateLeaves m).card = 3 := by simp [privateLeaves]
    omega
  · by_cases nonempty : hubs.Nonempty
    · obtain ⟨v,hv⟩ := nonempty
      obtain ⟨vIn,h,rfl⟩ := (hm v).mp hv
      have unique {k : Hub m} (kIn : (Sum.inr k : Vertices m) ∈ S) : k = h := by
        apply Sum.inr.inj
        exact Finset.card_le_one.mp (by omega : hubs.card ≤ 1) _ ((hm _).mpr ⟨kIn,k,rfl⟩) _ hv
      let target := insert (Sum.inr h) (insert (Sum.inl (.inr (group h))) (commonLeaves m))
      have sub : S ⊆ target := by
        rintro ((i|i)|k) mem
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩))
        · obtain ⟨w,wIn,e⟩ := neighbor_in_tree mem vIn (by intro h; cases h)
          rcases w with l|k
          · exact False.elim e
          · have eq : group k = i := e
            rw [unique wIn] at eq
            rw [← eq]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · obtain rfl := unique mem
          exact Finset.mem_insert_self _ _
      have c := Finset.card_le_card sub
      have s := Finset.card_insert_le (Sum.inr h) (insert (Sum.inl (.inr (group h))) (commonLeaves m))
      have t := Finset.card_insert_le (Sum.inl (.inr (group h))) (commonLeaves m)
      have cc : (commonLeaves m).card = 3 := by simp [commonLeaves]
      change S.card ≤ (insert (Sum.inr h) (insert (Sum.inl (.inr (group h))) (commonLeaves m))).card at c
      omega
    · apply Classical.byContradiction (p := S.card ≤ 5)
      intro large
      have multi : 1 < S.card := by omega
      obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp multi
      obtain ⟨w,hw,e⟩ := neighbor_in_tree hu hv ne
      rcases u with l|h
      · rcases w with r|k
        · cases l <;> cases r <;> exact e
        · exact nonempty ⟨_,(hm _).mpr ⟨hw,k,rfl⟩⟩
      · exact nonempty ⟨_,(hm _).mpr ⟨hu,h,rfl⟩⟩

theorem tree_budget (m : ℕ) : treeNumber (graph m) ≤ 5 := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro S mem
  exact isTree_card_bound S (Finset.mem_filter.mp mem).2

theorem independent_six (m : ℕ) : ¬ NoIndependentSix (graph m) := by
  rw [noIndependentSix_iff_no_independent_embedding,not_not]
  classical
  let e := (Fintype.equivFinOfCardEq (show Fintype.card (Fin 3 ⊕ Fin 3) = 6 by decide)).symm
  let f : Fin 6 ↪ Vertices m := ⟨fun i => .inl (e i), fun _ _ h => e.injective (Sum.inl.inj h)⟩
  refine ⟨f,fun i j => ?_⟩
  change ¬ adj (.inl (e i)) (.inl (e j))
  cases e i <;> cases e j <;> exact id

theorem graph_connected (m : ℕ) : (graph m).Connected := by
  let H := (graph m).induce {v : Vertices m | v ∉ (∅ : Finset (Vertices m))}
  let inclusion : H →g graph m := ⟨Subtype.val,fun h => h⟩
  have conn : H.Connected := (connectivity_at_least_three m).2 ∅ (by simp)
  refine @SimpleGraph.Connected.mk _ _ (fun x y => ?_) ⟨Sum.inr (.inl (0,0))⟩
  exact (conn.preconnected ⟨x,by simp⟩ ⟨y,by simp⟩).map inclusion

/-- Orders fifteen and sixteen both have graphs satisfying the two
catalogue bounds and admitting an independent six-set. -/
theorem catalogue_constraints_allow_independent_six (m : ℕ) :
    Fintype.card (Vertices m) = 15 + m ∧ (graph m).Connected ∧ vertexConnectivity (graph m) = 3 ∧
      treeNumber (graph m) ≤ 5 ∧ ¬ NoIndependentSix (graph m) := by
  have order : Fintype.card (Vertices m) = 15 + m := by
    simp [Fintype.card_sum]
    omega
  exact ⟨order,graph_connected m,exact_connectivity m,tree_budget m,independent_six m⟩

#print axioms catalogue_constraints_allow_independent_six

end Graffiti199Depleted.Catalogue.IndependenceObstruction
