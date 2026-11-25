import Std
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Graffiti444.Exact

def vertices (n : Nat) : List Nat := List.range n

/-- A graph on the labels 0,…,n−1, with symmetric, irreflexive adjacency. -/
structure Graph (n : Nat) where
  adj : Nat → Nat → Bool
  symm : ∀ u v, adj u v = adj v u
  noLoop : ∀ u, adj u u = false
  valid : ∀ u v, adj u v = true → u < n ∧ v < n

inductive Walk (a : Nat → Nat → Bool) : Nat → Nat → Prop
  | done (v : Nat) : Walk a v v
  | step {u v w : Nat} : a u v = true → Walk a v w → Walk a u w

def Connected {n} (G : Graph n) : Prop :=
  ∀ u v, u < n → v < n → Walk G.adj u v

def Is2Independent {n} (G : Graph n) (I : List Nat) : Prop :=
  (∀ u ∈ I, u < n) ∧ I.Nodup ∧
    ∀ u v w, u ∈ I → v ∈ I → w ∈ I →
      G.adj u v = true → G.adj u w = true → v = w

def neighbors {n} (G : Graph n) (u : Nat) : List Nat :=
  (vertices n).filter (G.adj u)

/-- Each increasing triple in this list, together with u, determines one K4. -/
def incidentK4s {n} (G : Graph n) (u : Nat) : List (Nat × Nat × Nat) :=
  let ns := neighbors G u
  ns.flatMap (fun a => ns.flatMap (fun b =>
    if decide (a < b) && G.adj a b then
      (ns.filter (fun c => decide (b < c) && G.adj a c && G.adj b c)).map (fun c => (a,b,c))
    else []))

theorem mem_incidentK4s {n} (G : Graph n) (u a b c : Nat) :
  (a,b,c) ∈ incidentK4s G u ↔
  a < n ∧ b < n ∧ c < n ∧ a < b ∧ b < c ∧
  G.adj u a = true ∧ G.adj u b = true ∧ G.adj u c = true ∧
  G.adj a b = true ∧ G.adj a c = true ∧ G.adj b c = true := by
  unfold incidentK4s
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, y, hy, hp⟩
    split at hp
    next h =>
      have hab := (Bool.and_eq_true_iff.mp h)
      simp only [List.mem_map, Prod.mk.injEq, List.mem_filter,
        Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hp
      obtain ⟨z,hz,hbc,hac,hbc',hxa,hyb,hzc⟩ := hp
      subst a; subst b; subst c
      have hn (x : Nat) : x ∈ neighbors G u ↔ x < n ∧ G.adj u x = true := by
        simp [neighbors, vertices]
      exact ⟨(hn _).mp hx |>.1, (hn _).mp hy |>.1, (hn _).mp hz |>.1,
        of_decide_eq_true hab.1,hbc,(hn _).mp hx |>.2,(hn _).mp hy |>.2,
        (hn _).mp hz |>.2,hab.2,hac,hbc'⟩
    next h => simp at hp
  · intro h
    rcases h with ⟨ha,hb,hc,hab,hbc,hua,hub,huc,hab',hac',hbc'⟩
    have hn (x : Nat) : x ∈ neighbors G u ↔ x < n ∧ G.adj u x = true := by
      simp [neighbors, vertices]
    refine ⟨a,(hn _).mpr ⟨ha,hua⟩,b,(hn _).mpr ⟨hb,hub⟩,?_⟩
    simp [hab, hbc, hab', hac', hbc', hn, hc, huc]

/-- No vertex can count itself as one of the three other vertices. -/
theorem no_self_in_incidentK4 {n} (G : Graph n) {u a b c}
    (h : (a,b,c) ∈ incidentK4s G u) : u ≠ a ∧ u ≠ b ∧ u ≠ c := by
  rcases (mem_incidentK4s G u a b c).mp h with ⟨_,_,_,_,_,ha,hb,hc,_,_,_⟩
  constructor
  · intro h; subst a; rw [G.noLoop] at ha; contradiction
  constructor
  · intro h; subst b; rw [G.noLoop] at hb; contradiction
  · intro h; subst c; rw [G.noLoop] at hc; contradiction

private theorem nodup_tagged_flatMap {α β : Type} {xs : List α} {f : α → List β}
    (tag : β → α) (hxs : xs.Nodup)
    (hf : ∀ a ∈ xs, (f a).Nodup)
    (htag : ∀ a b, b ∈ f a → tag b = a) : (xs.flatMap f).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨hf, ?_⟩
  apply hxs.imp
  intro a₁ a₂ h x hx y hy e
  subst y
  exact h ((htag _ _ hx).symm.trans (htag _ _ hy))

/-- The clique enumeration counts each incident clique once. -/
theorem incidentK4s_nodup {n} (G : Graph n) (u : Nat) :
    (incidentK4s G u).Nodup := by
  let ns := neighbors G u
  have hns : ns.Nodup := List.Pairwise.filter _ List.nodup_range
  unfold incidentK4s
  apply nodup_tagged_flatMap Prod.fst hns
  · intro a _
    apply nodup_tagged_flatMap (fun x => x.2.1) hns
    · intro b _
      split
      · exact List.Pairwise.map (fun c => (a,b,c))
          (fun c d (neq : c ≠ d) eq =>
            neq (congrArg (fun p : Nat × Nat × Nat => p.2.2) eq))
          (List.Pairwise.filter _ hns)
      · exact List.nodup_nil
    · intro b t ht
      split at ht
      · obtain ⟨c,_,he⟩ := List.mem_map.mp ht
        rw [← he]
      · simp at ht
  · intro a t ht
    obtain ⟨b,_,hh⟩ := List.mem_flatMap.mp ht
    split at hh
    · obtain ⟨c,_,he⟩ := List.mem_map.mp hh
      rw [← he]
    · simp at hh

def distinct : List Nat → List Nat
  | [] => []
  | u :: us => if u ∈ us then distinct us else u :: distinct us

theorem mem_distinct (x : Nat) (xs : List Nat) : x ∈ distinct xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    by_cases h : u ∈ us
    · simp [distinct, h, ih]
      intro e
      exact e ▸ h
    · simp [distinct, h, ih]

theorem distinct_nodup (xs : List Nat) : (distinct xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons u us ih =>
    by_cases h : u ∈ us
    · simpa [distinct, h] using ih
    · simpa [distinct, h, List.nodup_cons, mem_distinct] using ih

def cliqueDegree {n} (G : Graph n) (u : Nat) : Nat := (incidentK4s G u).length

def cliqueDegreeValues {n} (G : Graph n) : List Nat :=
  distinct ((vertices n).map (cliqueDegree G))

theorem degreeValues_exact {n} (G : Graph n) (k : Nat) :
    k ∈ cliqueDegreeValues G ↔ ∃ u, u < n ∧ cliqueDegree G u = k := by
  simp [cliqueDegreeValues, mem_distinct, vertices, List.mem_map]

theorem degreeValues_nodup {n} (G : Graph n) : (cliqueDegreeValues G).Nodup :=
  distinct_nodup _

/-- The upper bound in #444, stated equivalently for every 2-independent set. -/
def Conjecture444 : Prop :=
  ∀ (n : Nat), 3 < n → ∀ (G : Graph n), Connected G →
    ∀ I : List Nat, Is2Independent G I →
      I.length ≤ n - (cliqueDegreeValues G).length / 2

def masks : List Nat :=
  [15,1,15,3,15,7,15,15,7,3,7,8] ++ [14] ++ List.replicate 4 13 ++
  List.replicate 7 11 ++ List.replicate 10 7

def rawAdj (u v : Nat) : Bool :=
  if u == v then false
  else if u < 4 && v < 4 then true
  else if u < 4 then (masks[v-4]?.getD 0).testBit u
  else if v < 4 then (masks[u-4]?.getD 0).testBit v
  else (u < 16 && v < 16 && (u-4)/2 == (v-4)/2)

theorem rawAdjSymm (u v : Nat) : rawAdj u v = rawAdj v u := by
  by_cases h : u = v
  · subst v; rfl
  by_cases hu : u < 4 <;> by_cases hv : v < 4 <;>
    simp [rawAdj, h, Ne.symm h, hu, hv, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc,
      BEq.comm]

def adj (u v : Nat) : Bool := decide (u < 38) && decide (v < 38) && rawAdj u v

def witnessGraph : Graph 38 where
  adj := adj
  symm := by
    intro u v
    unfold adj
    rw [rawAdjSymm u v, Bool.and_comm (decide (u < 38))]
  noLoop := by intro u; simp [adj, rawAdj]
  valid := by
    intro u v h
    simp only [adj, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

def witnessSet : List Nat := (vertices 38).drop 4

theorem witnessLabels : ∀ u ∈ witnessSet, u < 38 := by
  intro u hu
  exact List.mem_range.mp (List.mem_of_mem_drop hu)

private theorem boundedEdges {u v w : Nat} (hu : 4 ≤ u) (hv : 4 ≤ v) (hw : 4 ≤ w)
    (huv : adj u v = true) (huw : adj u w = true) : v = w := by
  have huv' : u ≠ v ∧ (u-4)/2 = (v-4)/2 := by
    by_cases h : u = v
    · simp [adj, rawAdj, h] at huv
    · simp [adj, rawAdj, h, Nat.not_lt.mpr hu, Nat.not_lt.mpr hv] at huv
      exact ⟨h, huv.2.2⟩
  have huw' : u ≠ w ∧ (u-4)/2 = (w-4)/2 := by
    by_cases h : u = w
    · simp [adj, rawAdj, h] at huw
    · simp [adj, rawAdj, h, Nat.not_lt.mpr hu, Nat.not_lt.mpr hw] at huw
      exact ⟨h, huw.2.2⟩
  omega

theorem witnessIndependent : Is2Independent witnessGraph witnessSet := by
  refine ⟨witnessLabels, by decide, ?_⟩
  intro u v w hu hv hw huv huw
  have hset : ∀ x ∈ witnessSet, 4 ≤ x := by decide
  exact boundedEdges (hset u hu) (hset v hv) (hset w hw) huv huw

private theorem reachableCore :
  ∀ u : Fin 38, u.val = 0 ∨ adj u.val 0 = true ∨ adj u.val 1 = true ∨
    adj u.val 2 = true ∨ adj u.val 3 = true := by decide

theorem witnessConnected : Connected witnessGraph := by
  have toZero : ∀ u, u < 38 → Walk adj u 0 := by
    intro u h
    rcases reachableCore ⟨u,h⟩ with e | e | e | e | e
    · change u = 0 at e; subst u; exact Walk.done 0
    · exact Walk.step e (Walk.done 0)
    · exact Walk.step e (Walk.step (show adj 1 0 = true by decide) (Walk.done 0))
    · exact Walk.step e (Walk.step (show adj 2 0 = true by decide) (Walk.done 0))
    · exact Walk.step e (Walk.step (show adj 3 0 = true by decide) (Walk.done 0))
  have append : ∀ {u v w}, Walk adj u v → Walk adj v w → Walk adj u w := by
    intro u v w p q
    induction p with
    | done => exact q
    | step h _ ih => exact Walk.step h (ih q)
  have reverse : ∀ {u v}, Walk adj u v → Walk adj v u := by
    intro u v p
    induction p with
    | done => exact Walk.done _
    | @step u v w h _ ih =>
      exact append ih (Walk.step ((witnessGraph.symm v u).trans h) (Walk.done u))
  intro u v hu hv
  exact append (toZero u hu) (reverse (toZero v hv))

theorem countValues : (cliqueDegreeValues witnessGraph).length = 11 := by decide

theorem disproof : ¬ Conjecture444 := by
  intro conjecture
  have h := conjecture 38 (by decide) witnessGraph witnessConnected witnessSet witnessIndependent
  rw [countValues] at h
  exact (show ¬ witnessSet.length ≤ 38 - 11 / 2 by decide) h

#print axioms disproof

end Graffiti444.Exact
