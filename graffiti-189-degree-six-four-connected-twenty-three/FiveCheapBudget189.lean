import WideWing189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.WideWing
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary from OneSlack189

set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
namespace Graffiti189LongestPath.FiveCheapBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def layouts (i j s t : ℕ) : Prop :=
  (i=1 ∧ j=4 ∧ s=10 ∧ t=16) ∨ (i=7 ∧ j=10 ∧ s=1 ∧ t=16) ∨
    (i=13 ∧ j=16 ∧ s=1 ∧ t=7)

def flanks (i j : ℕ) : Finset ℕ := {i-1,i+1,j-1,j+1}
def targets (i j s t : ℕ) : Finset ℕ := insert s (insert t (flanks i j))
def allowed (i j s t : ℕ) : Finset ℕ := insert i (insert j (targets i j s t))

structure PairData {a b : V} (p : G.Walk a b) (H : Finset V) (x y : V)
    (i j s t : ℕ) : Prop where
  shape : layouts i j s t
  pathLen : p.length=17
  Hcard : H.card=5
  xH : x∈H
  yH : y∈H
  xy : x≠y
  off : ∀ z∈H,z∉p.support
  full : ∀ z,z∈p.support ∨ z∈H
  clique : ∀ u∈H,∀ v∈H,u≠v→G.Adj u v
  pinsX : Pins p x={i,j}
  pinsY : Pins p y={s,t}
  own : ∀ z∈H,(i∈Pins p z ∨ j∈Pins p z)→z=x

variable {a b x y : V} {p : G.Walk a b} {H : Finset V} {i j s t : ℕ}

theorem shape_bound (A : PairData p H x y i j s t) :
    0<i ∧ i<j ∧ j<17 ∧ 0<s ∧ s<t ∧ t<17 := by
  rcases A.shape with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;> decide

theorem index_bound (A : PairData p H x y i j s t) {m : ℕ} (hm : m∈allowed i j s t) :
    m≤17 := by
  rcases A.shape with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;>
    simp [allowed,targets,flanks] at hm <;> omega

theorem targets_card (A : PairData p H x y i j s t) : (targets i j s t).card=6 := by
  rcases A.shape with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;> decide

theorem adjacency_on_spine (A : PairData p H x y i j s t) (m : ℕ) (mn : m<17) :
    G.Adj (p.getVert m) (p.getVert (m+1)) :=
  p.adj_getVert_succ (A.pathLen.symm ▸ mn)

theorem pins_at (A : PairData p H x y i j s t) :
    i∈Pins p x ∧ j∈Pins p x ∧ s∈Pins p y ∧ t∈Pins p y := by
  simp [A.pinsX,A.pinsY]

theorem distinct_get (A : PairData p H x y i j s t) (hp : IsLongest p)
    {m n : ℕ} (mm : m≤17) (nn : n≤17) (ne : m≠n) : p.getVert m≠p.getVert n :=
  fun e => ne (hp.1.getVert_injOn (A.pathLen.symm ▸ mm) (A.pathLen.symm ▸ nn) e)

private theorem x_not_adj_of_index (A : PairData p H x y i j s t) (hp : IsLongest p)
    {m : ℕ} (ml : m≤17) (mi : m≠i) (mj : m≠j) :
    ¬G.Adj x (p.getVert m) := by
  intro e
  by_cases zz : m=17
  · have h := (Graffiti189LongestPath.no_endpoints hp (A.off _ A.xH)).2
    apply h
    simpa only [zz,←A.pathLen,Walk.getVert_length] using e
  have ll := A.pathLen
  have h : m∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩
  rw [A.pinsX] at h
  exact (mem_insert.mp h).elim mi (fun e => mj (mem_singleton.mp e))

theorem targets_exact (A : PairData p H x y i j s t) (hc : G.Connected) (hp : IsLongest p)
    (cap : ∀ v,(DistanceTwo G v).card≤6) :
    DistanceTwo G x=(targets i j s t).image p.getVert := by
  classical
  have pins := pins_at A
  obtain ⟨ii,ij,jj,ss,st,tt⟩ := shape_bound A
  have offx := A.off _ A.xH
  have flank (m : ℕ) (hm : m∈flanks i j) : p.getVert m∈FlankVertices p x := by
    simp only [flanks,mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl
    · exact mem_image.mpr ⟨_,mem_union_left _ (mem_image.mpr ⟨i,pins.1,rfl⟩),rfl⟩
    · exact mem_image.mpr ⟨_,mem_union_right _ (mem_image.mpr ⟨i,pins.1,rfl⟩),rfl⟩
    · exact mem_image.mpr ⟨_,mem_union_left _ (mem_image.mpr ⟨j,pins.2.1,rfl⟩),rfl⟩
    · exact mem_image.mpr ⟨_,mem_union_right _ (mem_image.mpr ⟨j,pins.2.1,rfl⟩),rfl⟩
  have other (m : ℕ) (hm : m∈Pins p y) (ne1 : m≠i) (ne2 : m≠j) (ml : m≤17) :
      p.getVert m∈DistanceTwo G x :=
    Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc
        (fun e => offx (e.symm ▸ p.getVert_mem_support m))
        (x_not_adj_of_index A hp ml ne1 ne2) (A.clique _ A.xH _ A.yH A.xy)
        (Graffiti189LongestPath.pin_data hm).2)
  have distinctS : s≠i ∧ s≠j ∧ t≠i ∧ t≠j := by
    rcases A.shape with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;> decide
  have sub : (targets i j s t).image p.getVert ⊆ DistanceTwo G x := by
    intro v vv
    obtain ⟨m,mm,rfl⟩ := mem_image.mp vv
    simp only [targets,mem_insert] at mm
    rcases mm with e|e|h
    · exact e.symm ▸ other s pins.2.2.1 distinctS.1 distinctS.2.1 (by omega)
    · exact e.symm ▸ other t pins.2.2.2 distinctS.2.2.1 distinctS.2.2.2 (by omega)
    · exact (mem_sdiff.mp (flanks_outside_boundary hc hp offx (flank m h))).1
  have ic : ((targets i j s t).image p.getVert).card=6 := by
    rw [card_image_of_injOn (fun m hm n hn e =>
      hp.1.getVert_injOn
        (A.pathLen.symm ▸ index_bound A (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr hm)))))
        (A.pathLen.symm ▸ index_bound A (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr hn))))) e),
      targets_card A]
  exact (eq_of_subset_of_card_le sub (by rw [ic]; exact cap x)).symm

theorem cheap_owner (A : PairData p H x y i j s t) (_hp : IsLongest p)
    {m : ℕ} (mij : m=i ∨ m=j) {z : V} (zh : z∈H)
    (adj : G.Adj (p.getVert m) z) : z=x := by
  have jm : m<17 := by obtain ⟨ii,ij,jj,_⟩ := shape_bound A; rcases mij with rfl|rfl <;> omega
  have ll := A.pathLen
  have pin : m∈Pins p z := mem_filter.mpr ⟨mem_range.mpr (by omega),adj.symm⟩
  exact A.own _ zh (mij.elim (fun e => Or.inl (e ▸ pin)) (fun e => Or.inr (e ▸ pin)))

/-- A cheap pin sees its own porter and only the eight specified spine
positions, including its own position as a harmless overestimate. -/
theorem cheap_neighbors (A : PairData p H x y i j s t) (hc : G.Connected) (hp : IsLongest p)
    (cap : ∀ v,(DistanceTwo G v).card≤6) {m : ℕ} (mij : m=i ∨ m=j)
    {v : V} (adj : G.Adj (p.getVert m) v) :
    v=x ∨ v∈(allowed i j s t).image p.getVert := by
  classical
  by_cases h : v∈H
  · exact Or.inl (cheap_owner A hp mij h adj)
  have vp := (A.full v).resolve_right h
  by_cases ax : G.Adj x v
  · obtain ⟨n,nP,en⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp (A.off _ A.xH) vp ax
    rw [A.pinsX] at nP
    exact Or.inr (mem_image.mpr ⟨n,by
      unfold allowed
      exact (mem_insert.mp nP).elim (fun h => mem_insert.mpr (Or.inl h))
        (fun h => mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl (mem_singleton.mp h))))),en⟩)
  have mx : m∈Pins p x := by
    rw [A.pinsX]
    exact mem_insert.mpr (mij.imp id mem_singleton.mpr)
  have ne : x≠v := fun e => A.off _ A.xH (e.symm ▸ vp)
  have dd : v ∈ DistanceTwo G x := Graffiti189LongestPath.mem_distanceTwo.mpr
    (Graffiti189LongestPath.dist_two hc ne
      ax (Graffiti189LongestPath.pin_data mx).2 adj)
  rw [targets_exact A hc hp cap] at dd
  obtain ⟨n,nt,eq⟩ := mem_image.mp dd
  exact Or.inr (mem_image.mpr ⟨n,mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr nt))),eq⟩)

noncomputable def residual (G : SimpleGraph V) (H : Finset V) (v : V) : Finset V := DistanceTwo G v\H

theorem residual_cap (A : PairData p H x y i j s t) (hc : G.Connected) (hp : IsLongest p)
    (cap : ∀ v,(DistanceTwo G v).card≤6) {m : ℕ} (mij : m=i ∨ m=j) :
    (residual G H (p.getVert m)).card≤2 := by
  classical
  have mx : m∈Pins p x := by
    rw [A.pinsX]
    exact mem_insert.mpr (mij.imp id mem_singleton.mpr)
  have sub : H.erase x⊆DistanceTwo G (p.getVert m) := by
    intro z hz
    obtain ⟨ne,zh⟩ := mem_erase.mp hz
    have ne0 : p.getVert m≠z := fun e => A.off _ zh (e ▸ p.getVert_mem_support m)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc ne0
        (fun ed => ne (cheap_owner A hp mij zh ed))
        (Graffiti189LongestPath.pin_data mx).2.symm (A.clique _ A.xH _ zh (Ne.symm ne)))
  have none : Disjoint (H.erase x) (residual G H (p.getVert m)) :=
    disjoint_left.mpr (fun _ zz rr => (mem_sdiff.mp rr).2 (mem_erase.mp zz).2)
  have c : (H.erase x ∪ residual G H (p.getVert m)).card≤6 := (card_le_card (union_subset sub sdiff_subset)).trans (cap (p.getVert m))
  rw [card_union_of_disjoint none,card_erase_of_mem A.xH,A.Hcard] at c
  omega

theorem charge_on_spine (A : PairData p H x y i j s t) (hc : G.Connected)
    {m r v : ℕ} (ne : p.getVert m≠p.getVert v)
    (mr : G.Adj (p.getVert m) (p.getVert r))
    (rv : G.Adj (p.getVert r) (p.getVert v)) (no : ¬G.Adj (p.getVert m) (p.getVert v)) :
    p.getVert v∈residual G H (p.getVert m) :=
  mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr
    (Graffiti189LongestPath.dist_two hc ne no mr rv),
    fun h => A.off _ h (p.getVert_mem_support v)⟩

#print axioms targets_exact
#print axioms cheap_neighbors
#print axioms residual_cap
end Graffiti189LongestPath.FiveCheapBudget
