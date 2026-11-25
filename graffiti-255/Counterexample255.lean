import Std
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Graffiti255
def vertices : List Nat := List.range 67
def rookColour (u : Nat) : Nat := (u/8+u%8)%2
def adj (u v : Nat) : Bool :=
  if u == v then false
  else if u < 64 && v < 64 then (u/8 == v/8) || (u%8 == v%8)
  else if u < 64 then v == 64+2*rookColour u
  else if v < 64 then u == 64+2*rookColour v
  else (u+1 == v) || (v+1 == u)
def reachesInTwo (u v : Nat) : Bool :=
  u == v || adj u v || vertices.any (fun w => adj u w && adj w v)
def edgeUnion (u v : Nat) : Nat :=
  (vertices.filter (fun w => adj u w || adj v w)).length
def boundedEdgeUnion : Bool :=
  vertices.all (fun u => vertices.all (fun v => !adj u v || edgeUnion u v ≤ 42))
def dominatingTriple : Bool :=
  vertices.all (fun u => [64,65,66].any (fun v => adj u v))
theorem connectedDiameterTwo :
    vertices.all (fun u => vertices.all (reachesInTwo u)) = true := by decide +kernel
theorem maxEdgeUnion : boundedEdgeUnion = true ∧ edgeUnion 0 64 = 42 := by
  constructor <;> decide +kernel
theorem upperBoundTotalDomination : dominatingTriple = true := by decide +kernel
theorem numericViolation : 3*42 < 2*67 := by decide

/-- Vertices are exactly 0,…,66, with no repetitions. -/
theorem vertexList : vertices.Nodup ∧ ∀ u, u ∈ vertices ↔ u < 67 :=
  ⟨List.nodup_range, fun _ => List.mem_range⟩

private theorem noUniversalCheck :
    vertices.all (fun u => vertices.any (fun v => (u != v) && !adj u v)) = true := by
  decide +kernel

private theorem symmetryCheck :
    vertices.all (fun u => vertices.all (fun v => adj u v == adj v u)) = true := by
  decide +kernel

theorem adjIrrefl (u : Nat) : adj u u = false := by simp [adj]

theorem adjSymm {u v : Nat} (hu : u ∈ vertices) (hv : v ∈ vertices) :
    adj u v = adj v u := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp symmetryCheck u hu) v hv
  simpa using h

/-- A walk of exactly k edges, with all vertices in the graph. -/
inductive Walk : Nat → Nat → Nat → Prop where
  | nil {v} : v ∈ vertices → Walk v v 0
  | cons {v w z k} : v ∈ vertices → adj v w = true → Walk w z k → Walk v z (k+1)

def EccAtMost (u k : Nat) : Prop :=
  ∀ v, v ∈ vertices → ∃ j, j ≤ k ∧ Walk u v j

/-- A center minimizes the maximum shortest-path distance. -/
def Center (u : Nat) : Prop :=
  u ∈ vertices ∧ ∃ k, EccAtMost u k ∧ ∀ v, v ∈ vertices → ∀ j, EccAtMost v j → k ≤ j

noncomputable def centerCount : Nat := by
  classical
  exact (vertices.filter (fun v => decide (Center v))).length

theorem eccAtMostTwo {u : Nat} (hu : u ∈ vertices) : EccAtMost u 2 := by
  intro v hv
  have h := List.all_eq_true.mp (List.all_eq_true.mp connectedDiameterTwo u hu) v hv
  change ((u == v || adj u v) || vertices.any (fun w => adj u w && adj w v)) = true at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Bool.or_eq_true] at h
    rcases h with h | h
    · have he : u = v := by simpa using h
      subst v
      exact ⟨0, by decide, Walk.nil hu⟩
    · exact ⟨1, by decide, Walk.cons hu h (Walk.nil hv)⟩
  · obtain ⟨w, hw, hwalk⟩ := List.any_eq_true.mp h
    rw [Bool.and_eq_true] at hwalk
    exact ⟨2, by decide, Walk.cons hu hwalk.1 (Walk.cons hw hwalk.2 (Walk.nil hv))⟩

theorem eccLowerTwo {u k : Nat} (hu : u ∈ vertices) (h : EccAtMost u k) : 2 ≤ k := by
  obtain ⟨v, hv, hbad⟩ := List.any_eq_true.mp (List.all_eq_true.mp noUniversalCheck u hu)
  rw [Bool.and_eq_true] at hbad
  have hne : u ≠ v := by simpa using hbad.1
  have hna : adj u v = false := by simpa using hbad.2
  obtain ⟨j, hj, hjw⟩ := h v hv
  cases hjw with
  | nil _ => exact (hne rfl).elim
  | @cons _ w _ j hh haj ht =>
    cases ht with
    | nil _ => simp [hna] at haj
    | cons _ _ _ => omega

theorem centers_exact : centerCount = 67 := by
  classical
  unfold centerCount
  rw [List.filter_eq_self.mpr]
  · rfl
  · intro u hu
    exact decide_eq_true ⟨hu, 2, eccAtMostTwo hu, fun _ hv _ he => eccLowerTwo hv he⟩

theorem connected : ∀ u v, u ∈ vertices → v ∈ vertices → ∃ k, Walk u v k :=
  fun _ v hu hv => let ⟨k, _, h⟩ := eccAtMostTwo hu v hv; ⟨k,h⟩

def Dominates (D : List Nat) : Prop :=
  ∀ v, v ∈ vertices → ∃ u, u ∈ D ∧ adj v u = true

/-- A total dominating set is represented by a duplicate-free list of vertices. -/
def ValidTotalDom (D : List Nat) : Prop :=
  D.Nodup ∧ (∀ u, u ∈ D → u ∈ vertices) ∧ Dominates D

def IsTotalDominationNumber (t : Nat) : Prop :=
  (∃ D, ValidTotalDom D ∧ D.length = t) ∧
  ∀ D, ValidTotalDom D → t ≤ D.length

/-- edgeUnion counts actual open neighborhood union, for the same adjacency used
in walks and dominating sets. -/
def IsLargestEdgeNeighborhood (m : Nat) : Prop :=
  (∃ u v, u ∈ vertices ∧ v ∈ vertices ∧ adj u v = true ∧ edgeUnion u v = m) ∧
  ∀ u v, u ∈ vertices → v ∈ vertices → adj u v = true → edgeUnion u v ≤ m

theorem edge_bound {u v : Nat} (hu : u ∈ vertices) (hv : v ∈ vertices)
    (h : adj u v = true) : edgeUnion u v ≤ 42 := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp maxEdgeUnion.1 u hu) v hv
  simpa [h] using hh

theorem largest_edge_neighborhood : IsLargestEdgeNeighborhood 42 := by
  refine ⟨⟨0, 64, by decide, by decide, by decide, maxEdgeUnion.2⟩, ?_⟩
  exact fun _ _ hu hv h => edge_bound hu hv h

theorem domination_exact : IsTotalDominationNumber 3 := by
  refine ⟨⟨[64,65,66], ⟨by decide, ?_, ?_⟩, rfl⟩, ?_⟩
  · intro u hu
    simp at hu
    rcases hu with rfl | rfl | rfl <;> decide
  · intro v hv
    exact List.any_eq_true.mp (List.all_eq_true.mp upperBoundTotalDomination v hv)
  · intro D hD
    rcases hD with ⟨_, hsubset, hd⟩
    cases D with
    | nil =>
      obtain ⟨u, hu, _⟩ := hd 0 (by decide)
      exact (List.not_mem_nil hu).elim
    | cons a D =>
      have ha := hsubset a (by simp)
      cases D with
      | nil =>
        obtain ⟨u, hu, h⟩ := hd a ha
        have he : u = a := List.mem_singleton.mp hu
        subst u
        simp [adjIrrefl] at h
      | cons b D =>
        have hb := hsubset b (by simp)
        cases D with
        | nil =>
          have hab : adj a b = true := by
            obtain ⟨u, hu, hh⟩ := hd a ha
            simp at hu
            rcases hu with rfl | rfl
            · simp [adjIrrefl] at hh
            · exact hh
          have hc : (vertices.filter (fun w => adj a w || adj b w)) = vertices := by
            apply List.filter_eq_self.mpr
            intro v hv
            obtain ⟨w, hw, hh⟩ := hd v hv
            simp at hw
            rcases hw with rfl | rfl
            · rw [adjSymm ha hv, hh]; rfl
            · rw [adjSymm hb hv, hh]; simp
          have hval := edge_bound ha hb hab
          unfold edgeUnion at hval
          rw [hc] at hval
          have : vertices.length = 67 := rfl
          omega
        | cons c D => simp

/-- Full exact counterexample: simple connected graph, 67 centers, exact total
domination number 3 and maximum edge-neighborhood 42, violating #255. -/
theorem counterexample255 :
    (∀ u, adj u u = false) ∧
    (∀ u v, u ∈ vertices → v ∈ vertices → adj u v = adj v u) ∧
    (∀ u v, u ∈ vertices → v ∈ vertices → ∃ k, Walk u v k) ∧
    centerCount = 67 ∧ IsTotalDominationNumber 3 ∧ IsLargestEdgeNeighborhood 42 ∧
    3*42 < 2*centerCount := by
  refine ⟨adjIrrefl, fun _ _ => adjSymm, connected, centers_exact, domination_exact,
    largest_edge_neighborhood, ?_⟩
  rw [centers_exact]
  exact numericViolation

#print axioms counterexample255
end Graffiti255
