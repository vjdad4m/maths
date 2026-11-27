import GraphPathLift
import Mathlib.Data.List.Sort
import Mathlib.Data.List.NodupEquivFin
import Lean.Elab.Tactic.Omega

namespace GraphPathLift
open SimpleGraph

variable {V W : Type*} [Fintype V]

/-- Edges to the preceding distance layer, counted for cage tie-breaking. -/
noncomputable def precedingDegree (G : SimpleGraph V) (r v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => G.dist r x + 1 = G.dist r v ∧ G.Adj v x)).card

theorem precedingDegree_le (G : SimpleGraph V) (r v : V) :
    precedingDegree G r v ≤ Fintype.card V := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Sort a finite graph by distance from `r`, and on every distance layer
by degree to the preceding layer. The root is label zero. -/
theorem exists_bfs_order (G : SimpleGraph V) (hc : G.Connected) (r : V) :
    ∃ (e : Fin (Fintype.card V) ≃ V),
      e ⟨0,Fintype.card_pos_iff.mpr ⟨r⟩⟩ = r ∧
      (∀ i j, i ≤ j → G.dist r (e i) ≤ G.dist r (e j)) ∧
      (∀ i j, i ≤ j → G.dist r (e i) = G.dist r (e j) →
        precedingDegree G r (e i) ≤ precedingDegree G r (e j)) := by
  classical
  let N := Fintype.card V
  let key (v : V) := (N+1)*G.dist r v + precedingDegree G r v
  let rel (v w : V) : Prop := key v ≤ key w
  letI : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
  letI : IsTotal V rel := ⟨fun x y => Nat.le_total (key x) (key y)⟩
  letI : IsTrans V rel := ⟨fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂⟩
  letI : IsRefl V rel := ⟨fun _ => Nat.le_refl _⟩
  let L₀ := (Finset.univ : Finset V).toList
  let L := L₀.mergeSort (fun x y => decide (rel x y))
  have perm : L.Perm L₀ := List.mergeSort_perm _ _
  have len : L.length = N := perm.length_eq.trans ((Finset.length_toList _).trans Finset.card_univ)
  have hh : L.Nodup := perm.symm.nodup (Finset.nodup_toList _)
  have hall (v : V) : v ∈ L := perm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))
  have sort : L.Sorted rel := List.sorted_mergeSort' rel L₀
  let f : Fin L.length ≃ V := hh.getEquivOfForallMemList L hall
  let cast : Fin N ≃ Fin L.length :=
    ⟨Fin.cast len.symm, Fin.cast len, fun i => Fin.ext rfl, fun i => Fin.ext rfl⟩
  let e : Fin N ≃ V := cast.trans f
  have mono (i j : Fin N) (h : i ≤ j) : key (e i) ≤ key (e j) := by
    change rel (L.get (cast i)) (L.get (cast j))
    exact sort.rel_get_of_le (show cast i ≤ cast j from h)
  have monoD (i j : Fin N) (h : i ≤ j) : G.dist r (e i) ≤ G.dist r (e j) := by
    have hk := mono i j h
    by_cases hn : G.dist r (e i) ≤ G.dist r (e j)
    · exact hn
    exfalso
    have hp : G.dist r (e j)+1 ≤ G.dist r (e i) := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
    have hmul := Nat.mul_le_mul_left (N+1) hp
    rw [Nat.mul_succ] at hmul
    have hprev := precedingDegree_le G r (e j)
    change precedingDegree G r (e j) ≤ N at hprev
    change (N+1)*G.dist r (e i) + precedingDegree G r (e i) ≤
      (N+1)*G.dist r (e j) + precedingDegree G r (e j) at hk
    omega
  refine ⟨e,?_,monoD,?_⟩
  · let zero : Fin N := ⟨0,Fintype.card_pos_iff.mpr ⟨r⟩⟩
    obtain ⟨j,hj⟩ := e.surjective r
    have hd := monoD zero j (Nat.zero_le _)
    rw [hj,SimpleGraph.dist_self] at hd
    change e zero = r
    by_cases hn : e zero = r
    · exact hn
    exfalso
    have hp := hc.pos_dist_of_ne (Ne.symm hn)
    omega
  · intro i j h hd
    have hk := mono i j h
    change (N+1)*G.dist r (e i) + precedingDegree G r (e i) ≤
      (N+1)*G.dist r (e j) + precedingDegree G r (e j) at hk
    rw [hd] at hk
    omega

omit [Fintype V] in
/-- A graph isomorphism transports distances on a connected graph. -/
theorem dist_iso (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (hc : G.Connected) (a b : V) : H.dist (e a) (e b) = G.dist a b := by
  have hh := hc.map e.toHom e.surjective
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨q,hq⟩ := hh.exists_walk_length_eq_dist (e a) (e b)
  have h₁ := H.dist_le (p.map e.toHom)
  rw [Walk.length_map,hp] at h₁
  have h₂ := G.dist_le (q.map e.symm.toHom)
  rw [Walk.length_map,hq] at h₂
  simpa using le_antisymm h₁ (by simpa using h₂)

variable [Fintype W]

theorem precedingDegree_iso (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (hc : G.Connected) (r v : V) :
    precedingDegree H (e r) (e v) = precedingDegree G r v := by
  classical
  unfold precedingDegree
  symm
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    rw [dist_iso G H e hc,dist_iso G H e hc]
    exact ⟨hx.1,e.toHom.map_adj hx.2⟩
  · intro a _ b _ h
    exact e.injective h
  · intro y hy
    obtain ⟨x,rfl⟩ := e.surjective y
    refine ⟨x,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy ⊢
    rw [dist_iso G H e hc,dist_iso G H e hc] at hy
    exact ⟨hy.1,e.map_rel_iff.mp hy.2⟩

/-- The relabeled cage graph has root zero, distance blocks in order, and
preceding-degree ties sorted as used by cage.py. -/
theorem exists_labelled_bfs_graph (G : SimpleGraph V) (hc : G.Connected) (r : V) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), ∃ e : H ≃g G,
      let z : Fin (Fintype.card V) := ⟨0,Fintype.card_pos_iff.mpr ⟨r⟩⟩
      (e z = r) ∧ H.Connected ∧
      (∀ i j, i ≤ j → H.dist z i ≤ H.dist z j) ∧
      (∀ i j, i ≤ j → H.dist z i = H.dist z j →
        precedingDegree H z i ≤ precedingDegree H z j) := by
  obtain ⟨e,hz,hd,hp⟩ := exists_bfs_order G hc r
  let e' := SimpleGraph.Iso.comap e G
  have hh := hc.map e'.symm.toHom e'.symm.surjective
  let z : Fin (Fintype.card V) := ⟨0,Fintype.card_pos_iff.mpr ⟨r⟩⟩
  have hr : e' z = r := hz
  have dist (i : Fin (Fintype.card V)) : G.dist r (e i) = _ :=
    hr ▸ dist_iso _ G e' hh z i
  have pr (i : Fin (Fintype.card V)) : precedingDegree G r (e i) = _ :=
    hr ▸ precedingDegree_iso _ G e' hh z i
  refine ⟨_,e',hr,hh,?_,?_⟩
  · intro i j h
    rw [← dist i,← dist j]
    exact hd i j h
  · intro i j h h'
    rw [← pr i,← pr j]
    apply hp i j h
    simpa only [dist] using h'

#print axioms exists_labelled_bfs_graph

private def indexPrefix {n k : ℕ} (hk : k ≤ n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin k)).map
    ⟨(fun x : Fin k => (⟨x.val,Nat.lt_of_lt_of_le x.isLt hk⟩ : Fin n)),
      by intro a b h; apply Fin.ext; exact congrArg (fun x : Fin n => x.val) h⟩

@[simp] private theorem indexPrefix_card {n k : ℕ} (hk : k ≤ n) :
    (indexPrefix hk).card = k := by simp [indexPrefix]

private theorem indexPrefix_mem {n k : ℕ} (hk : k ≤ n) (i : Fin n) :
    i ∈ indexPrefix hk ↔ i.val < k := by
  unfold indexPrefix
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j,_,hj⟩
    have h : j.val=i.val := congrArg Fin.val hj
    exact h ▸ j.isLt
  · intro h
    exact ⟨⟨i.val,h⟩,Finset.mem_univ _,Fin.ext rfl⟩

/-- An initial segment of Fin n is exactly the indices below its cardinality. -/
theorem prefix_filter_iff {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ i j, i ≤ j → P j → P i) (i : Fin n) :
    P i ↔ i.val < (Finset.univ.filter P).card := by
  constructor
  · intro hi
    let p := indexPrefix (Nat.succ_le_of_lt i.isLt)
    have hs : p ⊆ Finset.univ.filter P := by
      intro j hj
      have hji := (indexPrefix_mem _ j).mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP j i (Nat.le_of_lt_succ hji) hi⟩
    have h := Finset.card_le_card hs
    change (indexPrefix _).card ≤ _ at h
    rw [indexPrefix_card] at h
    exact h
  · intro hi
    by_cases hh : P i
    · exact hh
    let p := indexPrefix i.isLt.le
    have hs : Finset.univ.filter P ⊆ p := by
      intro j hj
      have hhj := (Finset.mem_filter.mp hj).2
      exact (indexPrefix_mem _ j).mpr (Nat.lt_of_not_ge (fun hji => hh (hP i j hji hhj)))
    have h := Finset.card_le_card hs
    change _ ≤ (indexPrefix _).card at h
    rw [indexPrefix_card] at h
    exact (not_lt_of_ge h hi).elim

/-- The distance layer in any sorted labeling is exactly its cumulative block. -/
theorem layer_eq_interval {n : ℕ} (H : SimpleGraph (Fin n)) (z : Fin n)
    (hs : ∀ i j, i ≤ j → H.dist z i ≤ H.dist z j) (i : Fin n) (d : ℕ) :
    H.dist z i = d ↔
      (Finset.univ.filter (fun j => H.dist z j < d)).card ≤ i.val ∧
      i.val < (Finset.univ.filter (fun j => H.dist z j ≤ d)).card := by
  have hlt := prefix_filter_iff (fun j => H.dist z j < d)
    (fun a b h hab => (hs a b h).trans_lt hab) i
  have hle := prefix_filter_iff (fun j => H.dist z j ≤ d)
    (fun a b h hab => (hs a b h).trans hab) i
  constructor
  · intro hi
    refine ⟨Nat.le_of_not_gt (fun h => ?_),hle.mp hi.le⟩
    exact (Nat.lt_irrefl d) (hi ▸ hlt.mpr h)
  · rintro ⟨ha,hb⟩
    exact Nat.le_antisymm (hle.mpr hb) (Nat.le_of_not_gt (fun e => (Nat.not_lt_of_ge ha) (hlt.mp e)))

omit [Fintype V] in
/-- Edges cannot skip distance layers. -/
theorem adj_distance_steps (G : SimpleGraph V) (hc : G.Connected) (r : V)
    {a b : V} (h : G.Adj a b) :
    G.dist r a ≤ G.dist r b + 1 ∧ G.dist r b ≤ G.dist r a + 1 := by
  have h₁ := hc.dist_triangle (u := r) (v := b) (w := a)
  have h₂ := hc.dist_triangle (u := r) (v := a) (w := b)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at h₁
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at h₂
  exact ⟨h₁,h₂⟩

omit [Fintype V] in
/-- Each non-root vertex has a neighbor in the preceding distance layer. -/
theorem exists_preceding_neighbor (G : SimpleGraph V) (hc : G.Connected) (r : V)
    {v : V} (hv : v ≠ r) : ∃ u, G.Adj v u ∧ G.dist r u + 1 = G.dist r v := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact (hv rfl).elim
  | cons e q =>
    rename_i w
    have hq := G.dist_le q
    have hcap := (adj_distance_steps G hc r e).1
    simp only [Walk.length_cons] at hp
    rw [SimpleGraph.dist_comm (u:=v) (v:=r)] at hp
    rw [SimpleGraph.dist_comm (u:=w) (v:=r)] at hq
    exact ⟨w,e,by omega⟩

#print axioms layer_eq_interval
#print axioms adj_distance_steps
#print axioms exists_preceding_neighbor

/-- The cardinality of every set of distances from a root is an isomorphism invariant. -/
theorem card_distance_filter_iso (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (hc : G.Connected) (r : V) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x => P (G.dist r x))).card =
    (Finset.univ.filter (fun y => P (H.dist (e r) y))).card := by
  classical
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simpa only [Finset.mem_univ,Finset.mem_filter,true_and,dist_iso G H e hc] using hx
  · intro x _ y _ he
    exact e.injective he
  · intro y hy
    obtain ⟨x,rfl⟩ := e.surjective y
    refine ⟨x,?_,rfl⟩
    simpa only [Finset.mem_univ,Finset.mem_filter,true_and,dist_iso G H e hc] using hy

private theorem split_counts {A : Type*} [Fintype A] (h : A → ℕ) (d : ℕ) :
      (Finset.univ.filter (fun x => h x < d+1)).card =
      (Finset.univ.filter (fun x => h x < d)).card +
        (Finset.univ.filter (fun x => h x = d)).card := by
    classical
    let S := Finset.univ.filter (fun x => h x < d)
    let T := Finset.univ.filter (fun x => h x = d)
    have hd : Disjoint S T := Finset.disjoint_left.mpr (fun a hs ht => by
      obtain h₁ := (Finset.mem_filter.mp hs).2
      obtain h₂ := (Finset.mem_filter.mp ht).2
      omega)
    have hh : (Finset.univ.filter (fun x => h x < d+1)) = S ∪ T := by
      ext x
      simp only [S,T,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
      omega
    exact (congrArg Finset.card hh).trans (Finset.card_union_of_disjoint hd)

/-- Counts for exact values determine cumulative counts. -/
theorem cumulative_of_exact_counts {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → ℕ) (g : Y → ℕ)
    (he : ∀ d, (Finset.univ.filter (fun x => f x = d)).card =
      (Finset.univ.filter (fun y => g y = d)).card) :
    ∀ d, (Finset.univ.filter (fun x => f x < d)).card =
      (Finset.univ.filter (fun y => g y < d)).card := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    exact (split_counts f d).trans (by rw [ih,he,← split_counts g d])

/-- Two nondecreasing layer assignments on the same labels with the same
exact layer counts agree at every index. -/
theorem ordered_layers_eq_of_card {n : ℕ} (f g : Fin n → ℕ)
    (hf : ∀ i j, i ≤ j → f i ≤ f j) (hg : ∀ i j, i ≤ j → g i ≤ g j)
    (hcard : ∀ d, (Finset.univ.filter (fun i => f i=d)).card =
      (Finset.univ.filter (fun i => g i=d)).card) :
    ∀ i, f i = g i := by
  intro i
  have hc := cumulative_of_exact_counts f g hcard
  have iff' (d : ℕ) : f i < d ↔ g i < d := by
    rw [prefix_filter_iff (fun j => f j < d) (fun a b h h' => (hf a b h).trans_lt h') i]
    rw [prefix_filter_iff (fun j => g j < d) (fun a b h h' => (hg a b h).trans_lt h') i]
    rw [hc]
  exact Nat.le_antisymm (Nat.le_of_not_gt (fun e => Nat.lt_irrefl _ ((iff' (f i)).mpr e)))
    (Nat.le_of_not_gt (fun e => Nat.lt_irrefl _ ((iff' (g i)).mp e)))

#print axioms card_distance_filter_iso
#print axioms ordered_layers_eq_of_card
end GraphPathLift
