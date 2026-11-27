import Substitution180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replace one color's neighbors of a new vertex by that vertex.
All previously pinned vertices from the independent marking survive. -/
theorem repair_color (G : SimpleGraph V) (I C D : Finset V) (v : V)
    (pin : Indep G (insert v I)) (inc : I⊆C∪D) (ci : Indep G C) (di : Indep G D)
    (dis : Disjoint C D) (out : v∉C∪D) (cheap : (C∩G.neighborFinset v).card≤1) :
    ∃ Z,TwoColor G Z ∧ insert v I⊆Z ∧ C.card+D.card≤Z.card := by
  classical
  let N := G.neighborFinset v
  let S := C\N
  have vc : v∉C := fun m => out (mem_union_left _ m)
  have vd : v∉D := fun m => out (mem_union_right _ m)
  have vs : v∉S := fun m => vc (mem_sdiff.mp m).1
  have si : Indep G (insert v S) := by
    intro x xm y ym ne edge
    rcases mem_insert.mp xm with xv|xs <;> rcases mem_insert.mp ym with yv|ys
    · exact ne (xv.trans yv.symm)
    · exact (mem_sdiff.mp ys).2 ((G.mem_neighborFinset _ _).mpr (xv ▸ edge))
    · exact (mem_sdiff.mp xs).2 ((G.mem_neighborFinset _ _).mpr (yv ▸ edge.symm))
    · exact ci x (mem_sdiff.mp xs).1 y (mem_sdiff.mp ys).1 ne edge
  have sep : Disjoint (insert v S) D := disjoint_insert_left.mpr ⟨vd,dis.mono_left sdiff_subset⟩
  refine ⟨insert v S∪D,⟨_,_,sep,rfl,si,di⟩,?_,?_⟩
  · intro x xm
    rcases mem_insert.mp xm with rfl|xi
    · exact mem_union_left _ (mem_insert_self ..)
    rcases mem_union.mp (inc xi) with xc|xd
    · apply mem_union_left
      apply mem_insert_of_mem
      refine mem_sdiff.mpr ⟨xc,fun n => ?_⟩
      have e := (G.mem_neighborFinset v x).mp n
      exact pin v (mem_insert_self ..) x (mem_insert_of_mem xi) e.ne e
    · exact mem_union_right _ xd
  · rw [card_union_of_disjoint sep,card_insert_of_not_mem vs]
    have count := card_sdiff_add_card_inter C N
    change S.card+(C∩N).card=C.card at count
    change (C∩N).card≤1 at cheap
    omega

/-- Any independent set of vertices of degree at most three occurs in
one maximum-order induced bipartite subgraph, even in a nonbipartite graph. -/
theorem pin_low_degree (G : SimpleGraph V) (I : Finset V) (ai : Indep G I) (low : ∀ x∈I,G.degree x≤3) :
    ∃ Z,TwoColor G Z ∧ Z.card=bipartiteNum G ∧ I⊆Z := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    obtain ⟨Z,c,e⟩ := optB G
    exact ⟨Z,c,e,empty_subset _⟩
  | @insert v I vi ih =>
    obtain ⟨Z,col,sz,inc⟩ := ih (fun x xm y ym => ai x (mem_insert_of_mem xm) y (mem_insert_of_mem ym))
      (fun x xm => low x (mem_insert_of_mem xm))
    by_cases vm : v∈Z
    · exact ⟨Z,col,sz,insert_subset vm inc⟩
    obtain ⟨C,D,dis,rfl,ci,di⟩ := col
    let N := G.neighborFinset v
    have separate : Disjoint (C∩N) (D∩N) := dis.mono inter_subset_left inter_subset_left
    have cap := card_le_card (show (C∩N)∪(D∩N)⊆N from union_subset inter_subset_right inter_subset_right)
    rw [card_union_of_disjoint separate] at cap
    have deg := low v (mem_insert_self ..)
    change N.card≤3 at deg
    have sizes := card_union_of_disjoint dis
    obtain ⟨W,ok,more,mass⟩ : ∃ W,TwoColor G W ∧ insert v I⊆W ∧ C.card+D.card≤W.card := by
      by_cases cheap : (C∩N).card≤1
      · exact repair_color G I C D v ai inc ci di dis vm cheap
      · have other : (D∩N).card≤1 := by omega
        obtain ⟨W,ok,inw,mass⟩ := repair_color G I D C v ai (union_comm C D ▸ inc) di ci dis.symm
          (union_comm C D ▸ vm) other
        exact ⟨W,ok,inw,by omega⟩
    exact ⟨W,ok,le_antisymm (size_bip G ok) (by omega),more⟩

/-- Only the indices of nonclique bags require a degree hypothesis. -/
theorem cover_degree_three {W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (f : W→V)
    (low : ∀ i,NonCliqueBag H f i → G.degree i≤3) : CoversBags H G f := by
  classical
  intro I ii
  let J := I.filter (NonCliqueBag H f)
  obtain ⟨Z,bi,sz,keep⟩ := pin_low_degree G J (fun x xm y ym => ii x (mem_filter.mp xm).1 y (mem_filter.mp ym).1)
    (fun x m => low x (mem_filter.mp m).2)
  exact ⟨Z,bi,sz,fun i im fat => keep (mem_filter.mpr ⟨im,fat⟩)⟩

theorem Bags.lowDegreeRooted {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} {G : SimpleGraph V}
    {f : W→V} (h : Bags H G f) (low : ∀ i,NonCliqueBag H f i → G.degree i≤3)
    (gc : G.Connected) (hn : 1<Fintype.card V) (r : W) (p : Bool)
    (old : localBound G (f r) (parity G (f r) p)) : localBound H r (parity H r p) :=
  h.rooted (cover_degree_three H G f low) gc hn r p old

#print axioms repair_color
#print axioms pin_low_degree
#print axioms cover_degree_three
#print axioms Bags.lowDegreeRooted
end Minimal180.Substitution
