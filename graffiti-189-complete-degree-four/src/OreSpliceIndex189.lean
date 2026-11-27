import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Lean.Elab.Tactic.Omega

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel H.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem getVert_injective_on {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) {i j : ℕ} (hi : i≤p.length) (hj : j≤p.length)
    (h : p.getVert i=p.getVert j) : i=j := by
  have hi' : i < p.support.length := by rw [length_support]; omega
  have hj' : j < p.support.length := by rw [length_support]; omega
  have eqi : p.getVert i = p.support[i] := Option.some.inj
    ((getVert_eq_support_get? p hi).trans (List.getElem?_eq_getElem hi'))
  have eqj : p.getVert j = p.support[j] := Option.some.inj
    ((getVert_eq_support_get? p hj).trans (List.getElem?_eq_getElem hj'))
  exact hp.support_nodup.getElem_inj_iff.mp (eqi.symm.trans (h.trans eqj))

omit [DecidableEq V] in
/-- Two endpoint neighborhoods hitting a spanning path in more slots than there
are consecutive pairs force an Ore splice. The counted graph and the ambient
path graph need not coincide. -/
theorem ore_splice_index {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (all : ∀ v, v ∈ p.support) (big : p.length < H.degree a + H.degree b) :
    ∃ i < p.length, H.Adj a (p.getVert (i+1)) ∧ H.Adj b (p.getVert i) := by
  let A := (range p.length).filter (fun i=>H.Adj a (p.getVert (i+1)))
  let B := (range p.length).filter (fun i=>H.Adj b (p.getVert i))
  have ca : A.card = H.degree a := by
    rw [← card_neighborFinset_eq_degree]
    apply card_bij (fun i _=>p.getVert (i+1))
    · intro i hi
      exact (mem_neighborFinset H a _).mpr (mem_filter.mp hi).2
    · intro i hi j hj eq
      have il := mem_range.mp (mem_filter.mp hi).1
      have jl := mem_range.mp (mem_filter.mp hj).1
      have q := getVert_injective_on p hp (by omega) (by omega) eq
      omega
    · intro z hz
      have adj := (mem_neighborFinset H a _).mp hz
      obtain ⟨k,rfl,hk⟩ := mem_support_iff_exists_getVert.mp (all z)
      have kn : k≠0 := by
        rintro rfl
        simp at adj
      refine ⟨k-1,?_,?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_range.mpr (by omega),?_⟩
        convert adj using 2
        omega
      · congr 1
        omega
  have cb : B.card = H.degree b := by
    rw [← card_neighborFinset_eq_degree]
    apply card_bij (fun i _=>p.getVert i)
    · intro i hi
      exact (mem_neighborFinset H b _).mpr (mem_filter.mp hi).2
    · intro i hi j hj eq
      have il := mem_range.mp (mem_filter.mp hi).1
      have jl := mem_range.mp (mem_filter.mp hj).1
      exact getVert_injective_on p hp (by omega) (by omega) eq
    · intro z hz
      have adj := (mem_neighborFinset H b _).mp hz
      obtain ⟨k,rfl,hk⟩ := mem_support_iff_exists_getVert.mp (all z)
      have kn : k≠p.length := by
        rintro rfl
        simp at adj
      exact ⟨k,mem_filter.mpr ⟨mem_range.mpr (by omega),adj⟩,rfl⟩
  have nd : ¬Disjoint A B := by
    intro dis
    have sub : A∪B ⊆ range p.length := by
      intro i h
      exact (mem_union.mp h).elim (fun ha=>(mem_filter.mp ha).1) (fun hb=>(mem_filter.mp hb).1)
    have cap := card_le_card sub
    rw [card_union_of_disjoint dis,ca,cb,card_range] at cap
    omega
  obtain ⟨i,ha,hb⟩ := not_disjoint_iff.mp nd
  exact ⟨i,mem_range.mp (mem_filter.mp ha).1,(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩

#print axioms ore_splice_index
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V}

private theorem split_path_edge {a b : V} (p : G.Walk a b) (j : ℕ) (hj : j < p.length) :
    (p.take j).append (.cons (p.adj_getVert_succ hj) (p.drop (j+1))) = p := by
  induction p generalizing j with
  | nil => simp at hj
  | @cons a u b e p ih =>
    cases j with
    | zero =>
      have h : HEq (p.drop 0) p := by cases p <;> rfl
      simpa [Walk.take, Walk.drop] using h
    | succ j =>
      have hj' : j < p.length := by simpa using hj
      exact congrArg (Walk.cons e) (ih j hj')

/-- The endpoint splice uses a prefix followed by the reversed suffix,
without losing or repeating vertices. -/
theorem ore_spliced_path {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (i : ℕ) (hi : i < p.length)
    (jump : G.Adj b (p.getVert i)) :
    ∃ q : G.Walk a (p.getVert (i+1)), q.IsPath ∧
      ∀ v, v ∈ q.support ↔ v ∈ p.support := by
  let l := p.take i
  let r := p.drop (i+1)
  let q := l.append (.cons jump.symm r.reverse)
  have split := split_path_edge p i hi
  have ps : p.support = l.support ++ r.support := by
    conv_lhs => rw [←split]
    simp only [support_append, support_cons, List.tail_cons, l, r]
  have qs : q.support = l.support ++ r.support.reverse := by
    simp only [q, support_append, support_cons, List.tail_cons, support_reverse]
  refine ⟨q, ?_, ?_⟩
  · rw [isPath_def, qs, List.nodup_append]
    have h := hp.support_nodup
    rw [ps, List.nodup_append] at h
    exact ⟨h.1, List.nodup_reverse.mpr h.2.1,
      fun x hx hy => h.2.2 hx (List.mem_reverse.mp hy)⟩
  · intro v
    simp [qs, ps]

#print axioms ore_spliced_path
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V}

/-- A closed spanning walk whose tail visits every vertex exactly once. -/
def SpanningRing {a : V} (p : G.Walk a a) : Prop :=
  p.support.tail.Nodup ∧ ∀ v, v ∈ p.support.tail

theorem ore_ring [Fintype V] [DecidableRel G.Adj] {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (all : ∀ v, v ∈ p.support)
    (big : p.length < G.degree a + G.degree b) :
    ∃ c : G.Walk a a, SpanningRing c := by
  obtain ⟨i,hi,ha,hb⟩ := ore_splice_index (H:=G) p hp all big
  obtain ⟨q,hq,hs⟩ := ore_spliced_path p hp i hi hb
  refine ⟨.cons ha q.reverse,?_⟩
  constructor
  · simpa only [support_cons,List.tail_cons,support_reverse,List.nodup_reverse] using hq.support_nodup
  · intro v
    simpa only [support_cons,List.tail_cons,support_reverse,List.mem_reverse] using (hs v).mpr (all v)

#print axioms ore_ring
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V}

private theorem edge_at_index {a b : V} (p : G.Walk a b) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ j < p.length, s(p.getVert j,p.getVert (j+1)) = e := by
  induction p with
  | nil => simp at he
  | @cons u v w uv p ih =>
    rcases List.mem_cons.mp he with h|h
    · exact ⟨0, by simp, by simpa using h.symm⟩
    · obtain ⟨j,hj,hs⟩ := ih h
      exact ⟨j+1, by simpa using hj, by simpa using hs⟩

/-- Cutting a cyclic spanning order at any edge produces a spanning path;
every remaining edge is drawn from the prefix or suffix at that cut. -/
theorem cut_spanning_ring {a : V} {c : G.Walk a a} (hc : SpanningRing c)
    {e : Sym2 V} (he : e ∈ c.edges) (nod : c.edges.Nodup) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧
      (∀ v, v ∈ p.support) ∧ s(x,y)=e ∧
      (∀ f ∈ p.edges, f ∈ c.edges ∧ f≠e) := by
  classical
  obtain ⟨j,hj,hj'⟩ := edge_at_index c he
  let l := c.take j
  let r := c.drop (j+1)
  let p := r.append l
  have split := split_path_edge c j hj
  have cs : c.support = l.support ++ r.support := by
    conv_lhs => rw [←split]
    simp only [support_append, support_cons, List.tail_cons, l,r]
  have tail : c.support.tail = l.support.tail ++ r.support := by
    rw [cs, support_eq_cons l]; rfl
  have ps : p.support = r.support ++ l.support.tail := by
    simp only [p,support_append]
  have perm : p.support.Perm c.support.tail := by
    rw [ps,tail]
    exact List.perm_append_comm
  have ces : c.edges = l.edges ++ (e :: r.edges) := by
    conv_lhs => rw [←split]
    simp only [edges_append, edges_cons, l,r,hj']
  have pes : p.edges = r.edges ++ l.edges := by
    simp only [p,edges_append]
  refine ⟨_,_,p, IsPath.mk' (perm.nodup_iff.mpr hc.1), fun v => perm.mem_iff.mpr (hc.2 v), ?_, ?_⟩
  · rw [Sym2.eq_swap]
    exact hj'
  · intro f hf
    have nod' := nod
    rw [ces,List.nodup_append,List.nodup_cons] at nod'
    rw [pes] at hf
    rcases List.mem_append.mp hf with fr|fl
    · exact ⟨ces ▸ List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr fr))),
        fun eq=>nod'.2.1.1 (eq ▸ fr)⟩
    · exact ⟨ces ▸ List.mem_append.mpr (Or.inl fl),
        fun eq=>nod'.2.2 fl (List.mem_cons.mpr (Or.inl eq))⟩

#print axioms cut_spanning_ring
end Graffiti189Ore
