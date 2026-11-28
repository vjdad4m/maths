import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sum
import Lean.Elab.Tactic.Omega

/-! Graph-to-interval stage for Pósa's ordered routes. Unverified source draft.
A label is either one off-spine connected component or one directed spine chord.
-/
namespace PosaBridges189
open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {N : ℕ} (p : Fin (N+1) ↪ V)

abbrev Outside := (Set.range p)ᶜ
abbrev Off := G.induce (Outside p)
abbrev Component := (Off (G := G) p).ConnectedComponent
abbrev Label := (Component (G := G) p) ⊕ (Fin (N+1) × Fin (N+1))

def Attached (C : Component (G := G) p) (a : Fin (N+1)) : Prop :=
  ∃ z : Outside p, (Off (G := G) p).connectedComponentMk z = C ∧ G.Adj (p a) z.val

noncomputable def attachments (C : Component (G := G) p) : Finset (Fin (N+1)) := by
  classical
  exact Finset.univ.filter (Attached (G := G) p C)

theorem mem_attachments {C : Component (G := G) p} {a : Fin (N+1)} :
    a ∈ attachments p C ↔ Attached p C a := by
  classical
  simp [attachments]

/-- An interval source has a simple detour; any non-endpoint vertex
of the detour lies in precisely the off-spine component on its label.
For a chord label there are no non-endpoint vertices. -/
structure Bridge (a b : Fin (N+1)) (s : Label (G := G) p) where
  lt : a < b
  walk : G.Walk (p a) (p b)
  isPath : walk.IsPath
  interior : ∀ v ∈ walk.support, v ≠ p a → v ≠ p b →
    ∃ z : Outside p, z.val = v ∧
      s = .inl ((Off (G := G) p).connectedComponentMk z)

private theorem same_component_of_mem_walk {s t : Outside p}
    (q : (Off (G := G) p).Walk s t) {z : Outside p} (hz : z ∈ q.support) :
    (Off (G := G) p).connectedComponentMk z =
      (Off (G := G) p).connectedComponentMk s := by
  classical
  exact ConnectedComponent.sound (show (Off (G := G) p).Reachable s z from
    ⟨q.takeUntil z hz⟩).symm

theorem comp_bridge {C : Component (G := G) p} {a b : Fin (N+1)}
    (ab : a < b) (ha : Attached p C a) (hb : Attached p C b) :
    Nonempty (Bridge p a b (.inl C)) := by
  classical
  obtain ⟨x, hx, ax⟩ := ha
  obtain ⟨y, hy, by'⟩ := hb
  obtain ⟨q⟩ := ConnectedComponent.exact (hx.trans hy.symm)
  let f : Off (G := G) p →g G := ⟨Subtype.val, fun h => h⟩
  let w : G.Walk (p a) (p b) :=
    .cons ax ((q.map f).concat by'.symm)
  refine ⟨⟨ab, w.toPath, w.toPath.2, ?_⟩⟩
  intro v hv hna hnb
  have hm := Walk.support_toPath_subset w hv
  simp only [w, Walk.support_cons, Walk.support_concat, List.concat_eq_append,
    List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hm
  rcases hm with h | hm
  · exact (hna h).elim
  rcases hm with hm | h
  · rw [Walk.support_map] at hm
    obtain ⟨z, hz, eq⟩ := List.mem_map.mp hm
    have same := same_component_of_mem_walk p q hz
    exact ⟨z, eq, congrArg Sum.inl (same.trans hx).symm⟩
  · exact (hnb h).elim

theorem chord_bridge {a b : Fin (N+1)} (ab : a < b) (h : G.Adj (p a) (p b)) :
    Nonempty (Bridge (G := G) p a b (.inr (a,b))) := by
  refine ⟨⟨ab, .cons h .nil, (Walk.IsPath.nil).cons (by simpa using h.ne), ?_⟩⟩
  intro v hv va vb
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  exact (hv.elim va vb).elim

private theorem walk_preserves {H : SimpleGraph V} (P : V → Prop)
    (closed : ∀ {a b : V}, H.Adj a b → P a → P b)
    {a b : V} (q : H.Walk a b) (ha : P a) : P b := by
  induction q with
  | nil => exact ha
  | cons e q ih => exact ih (closed e ha)

/-- Off-spine coloring argument: a deleted interior index is straddled
either by a spine chord or by two attachments in the same component. -/
theorem straddler {i : Fin (N+1)} (hi : 0 < i.val) (hiN : i.val < N)
    (conn : (G.induce ({p i}ᶜ : Set V)).Connected) :
    (∃ a b : Fin (N+1), a < i ∧ i < b ∧ G.Adj (p a) (p b)) ∨
      (∃ (C : Component (G := G) p) (a b : Fin (N+1)),
        a < i ∧ i < b ∧ Attached p C a ∧ Attached p C b) := by
  classical
  by_contra no
  let D := ({p i}ᶜ : Set V)
  let P (z : D) : Prop :=
    (∃ a : Fin (N+1), a < i ∧ p a = z.val) ∨
      ∃ w : Outside p, w.val = z.val ∧
        ∃ a : Fin (N+1), a < i ∧
          Attached p ((Off (G := G) p).connectedComponentMk w) a
  have step {z t : D} (e : (G.induce D).Adj z t) (hz : P z) : P t := by
    have adj : G.Adj z.val t.val := e
    by_cases ht : t.val ∈ Set.range p
    · obtain ⟨b, eb⟩ := ht
      have bi : b ≠ i := by
        intro eq
        subst b
        exact t.property (by simpa only [Set.mem_singleton_iff] using eb.symm)
      by_cases bl : b < i
      · exact Or.inl ⟨b, bl, eb⟩
      have ib : i < b := lt_of_le_of_ne (le_of_not_gt bl) (Ne.symm bi)
      rcases hz with ⟨a, ai, ea⟩ | ⟨w, ew, a, ai, att⟩
      · apply (no (Or.inl ⟨a,b,ai,ib,?_⟩)).elim
        simpa only [ea,eb] using adj
      · apply (no (Or.inr ⟨_,a,b,ai,ib,att,?_⟩)).elim
        exact ⟨w,rfl,by simpa only [ew,eb] using adj.symm⟩
    · let w : Outside p := ⟨t.val, ht⟩
      refine Or.inr ⟨w,rfl,?_⟩
      rcases hz with ⟨a,ai,ea⟩ | ⟨u,eu,a,ai,att⟩
      · exact ⟨a,ai,w,rfl,by simpa only [ea] using adj⟩
      · have edge : (Off (G := G) p).Adj u w := by
          change G.Adj u.val t.val
          simpa only [eu] using adj
        have eq : (Off (G := G) p).connectedComponentMk u =
            (Off (G := G) p).connectedComponentMk w :=
          ConnectedComponent.sound edge.reachable
        exact ⟨a,ai,eq ▸ att⟩
  let a : Fin (N+1) := ⟨0, by omega⟩
  let b : Fin (N+1) := ⟨N, by omega⟩
  have ai : a < i := hi
  have ib : i < b := hiN
  have memD {v : Fin (N+1)} (ne : v ≠ i) : p v ∈ D := by
    intro eq
    exact ne (p.injective (Set.mem_singleton_iff.mp eq))
  let s : D := ⟨p a, memD ai.ne⟩
  let t : D := ⟨p b, memD ib.ne.symm⟩
  obtain ⟨q⟩ := conn.preconnected s t
  have reached : P t := walk_preserves P (fun e h => step e h) q (Or.inl ⟨a,ai,rfl⟩)
  rcases reached with ⟨a',a'i,e⟩ | ⟨w,we,_⟩
  · have e' : a' = b := p.injective e
    exact (not_lt_of_ge ib.le) (e' ▸ a'i)
  · exact w.property ⟨b, we.symm⟩


noncomputable def ends : Label (G := G) p → Fin (N+1) × Fin (N+1)
  | .inr ab => ab
  | .inl C => by
      classical
      let T := attachments p C
      exact if h : T.Nonempty then (T.min' h, T.max' h) else (0,0)

private theorem extremes {C : Component (G := G) p} {a b : Fin (N+1)}
    (ha : Attached p C a) (hb : Attached p C b) :
    let e := ends p (.inl C)
    Attached p C e.1 ∧ Attached p C e.2 ∧ e.1 ≤ a ∧ b ≤ e.2 := by
  classical
  let T := attachments p C
  have am : a ∈ T := mem_attachments p |>.mpr ha
  have bm : b ∈ T := mem_attachments p |>.mpr hb
  have h : T.Nonempty := ⟨a,am⟩
  change Attached p C (ends p (.inl C)).1 ∧ Attached p C (ends p (.inl C)).2 ∧
    (ends p (.inl C)).1 ≤ a ∧ b ≤ (ends p (.inl C)).2
  simp only [ends, dif_pos (show (attachments p C).Nonempty from h)]
  exact ⟨(mem_attachments p).mp (Finset.min'_mem T h),
    (mem_attachments p).mp (Finset.max'_mem T h),
    Finset.min'_le T a am, Finset.le_max' T b bm⟩

/-- A finite concrete family usable by the independent greedy lemma.
There is at most one label for a component, even if its attachments
include many acceptable pairs. -/
structure Family where
  sources : Finset (Label (G := G) p)
  detour : ∀ a ∈ sources, Nonempty (Bridge p (ends p a).1 (ends p a).2 a)
  coverage : ∀ i : ℕ, 0 < i → i < N →
    ∃ a ∈ sources, (ends p a).1.val < i ∧ i < (ends p a).2.val

theorem exists_family [Finite V]
    (conn : ∀ i : Fin (N+1), 0 < i.val → i.val < N →
      (G.induce ({p i}ᶜ : Set V)).Connected) :
    Nonempty (Family (G := G) p) := by
  classical
  let C := Component (G := G) p
  letI : Finite C := Finite.of_surjective
    (Off (G := G) p).connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype C := Fintype.ofFinite C
  let S : Finset (Label (G := G) p) :=
    Finset.univ.filter (fun a => Nonempty (Bridge p (ends p a).1 (ends p a).2 a))
  refine ⟨⟨S, ?_, ?_⟩⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro i hi hiN
    let j : Fin (N+1) := ⟨i, by omega⟩
    rcases straddler p hi hiN (conn j hi hiN) with
      ⟨a,b,aj,jb,ab⟩ | ⟨c,a,b,aj,jb,ha,hb⟩
    · have ex := chord_bridge p (aj.trans jb) ab
      exact ⟨.inr (a,b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ex⟩, aj, jb⟩
    · let e := ends p (.inl c)
      obtain ⟨el,er,ale,ble⟩ := extremes p ha hb
      have lj : e.1 < j := lt_of_le_of_lt ale aj
      have jr : j < e.2 := lt_of_lt_of_le jb ble
      have ex := comp_bridge p (lj.trans jr) el er
      exact ⟨.inl c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ex⟩, lj, jr⟩

/-- Distinct labels have disjoint non-endpoint supports. -/
theorem interior_disjoint {a b c d : Fin (N+1)} {s t : Label (G := G) p}
    (q : Bridge p a b s) (q' : Bridge p c d t) (ne : s ≠ t)
    {v : V} (hv : v ∈ q.walk.support) (hv' : v ∈ q'.walk.support)
    (ha : v ≠ p a) (hb : v ≠ p b) (hc : v ≠ p c) (hd : v ≠ p d) : False := by
  obtain ⟨z, ez, hs⟩ := q.interior v hv ha hb
  obtain ⟨z', ez', ht⟩ := q'.interior v hv' hc hd
  have eq : z = z' := Subtype.ext (ez.trans ez'.symm)
  subst z'
  exact ne (hs.trans ht.symm)

end PosaBridges189

#print axioms PosaBridges189.exists_family
#print axioms PosaBridges189.interior_disjoint
