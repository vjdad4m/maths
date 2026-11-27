import Dependency180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
/-- Simultaneous deletion preserves every distance to the surviving root
exactly when every other survivor retains an immediate predecessor. -/
theorem retained_iff (hc : G.Connected) (S : Set V) (r : S) :
    ((G.induce S).Connected ∧ ∀ v : S, (G.induce S).dist v r=G.dist v.val r.val) ↔
      ∀ v : S, v≠r → ∃ w : S, G.Adj v.val w.val ∧ G.dist v.val r.val=G.dist w.val r.val+1 := by
  constructor
  · rintro ⟨conn,dist⟩ v ne
    obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor _ conn r v ne
    exact ⟨w,e,by rwa [dist,dist] at d⟩
  · intro keep
    apply layers _ r (fun v : S => G.dist v.val r.val) G.dist_self _ keep
    intro v w e
    have tri := hc.dist_triangle (u:=v.val) (v:=w.val) (w:=r.val)
    rw [dist_eq_one_iff_adj.mpr (show G.Adj v.val w.val from e)] at tri
    change G.dist v.val r.val≤G.dist w.val r.val+1
    omega

omit [Fintype V] [DecidableEq V] in
theorem sink_deletion (hc : G.Connected) (r z : V) (rz : r≠z) (sink : ∀ v, ¬Arc G r z v) :
    let S := ({z}ᶜ : Set V)
    let p : S := ⟨r,rz⟩
    (G.induce S).Connected ∧ ∀ v : S, (G.induce S).dist v p=G.dist v.val r := by
  dsimp only
  apply (retained_iff G hc _ ⟨r,rz⟩).mpr
  intro v ne
  have vr : v.val≠r := fun h => ne (Subtype.ext h)
  obtain ⟨q,vq,d⟩ := Graffiti169.exists_predecessor G hc r v.val vr
  by_cases qz : q=z
  · subst q
    have alt : ∃ x, G.Adj x v.val ∧ G.dist v.val r=G.dist x r+1 ∧ x≠z := by
      by_contra! no
      exact sink v.val ⟨vq.symm,d,no⟩
    obtain ⟨x,e,xd,xz⟩ := alt
    exact ⟨⟨x,xz⟩,e.symm,xd⟩
  · exact ⟨⟨q,qz⟩,vq,d⟩

private theorem swap_in [DecidableRel G.Adj] (w : V) (C D : Finset V)
    (ic : Indep G C) (id : Indep G D) (dis : Disjoint C D) (wc : w∉C) (wd : w∉D)
    (small : (C ∩ G.neighborFinset w).card≤1) :
    ∃ X, TwoColor G X ∧ w∈X ∧ C.card+D.card≤X.card := by
  classical
  let S := C \ G.neighborFinset w
  let E := insert w S
  have ws : w∉S := fun h => wc (mem_sdiff.mp h).1
  have es : Indep G E := by
    intro x hx y hy ne e
    rcases mem_insert.mp hx with rfl|xs <;> rcases mem_insert.mp hy with rfl|ys
    · exact ne rfl
    · exact (mem_sdiff.mp ys).2 ((G.mem_neighborFinset _ _).mpr e)
    · exact (mem_sdiff.mp xs).2 ((G.mem_neighborFinset _ _).mpr e.symm)
    · exact ic x (mem_sdiff.mp xs).1 y (mem_sdiff.mp ys).1 ne e
  have ed : Disjoint E D := disjoint_left.mpr (fun v ve vd =>
    (mem_insert.mp ve).elim (fun h => wd (h ▸ vd))
      (fun hs => disjoint_left.mp dis (mem_sdiff.mp hs).1 vd))
  have size := card_sdiff_add_card_inter C (G.neighborFinset w)
  change S.card+_=C.card at size
  refine ⟨E ∪ D,⟨E,D,ed,rfl,es,id⟩,mem_union_left _ (mem_insert_self _ _),?_⟩
  rw [card_union_of_disjoint ed]
  change _≤(insert w S).card+D.card
  rw [card_insert_of_not_mem ws]
  omega

/-- A vertex absent from every maximum induced bipartite set has at least
two neighbors of each color in every maximum coloring. -/
theorem excluded_colors [DecidableRel G.Adj] (w : V) (never : ∀ X, MaxSet G X → w∉X)
    (C D : Finset V) (ic : Indep G C) (id : Indep G D) (dis : Disjoint C D)
    (top : C.card+D.card=bipartiteNum G) :
    2≤(C ∩ G.neighborFinset w).card ∧ 2≤(D ∩ G.neighborFinset w).card := by
  classical
  have out := never (C ∪ D) ⟨⟨C,D,dis,rfl,ic,id⟩,(card_union_of_disjoint dis).trans top⟩
  have wc : w∉C := fun h => out (mem_union_left _ h)
  have wd : w∉D := fun h => out (mem_union_right _ h)
  have no (X : Finset V) (col : TwoColor G X) (mem : w∈X) (b : bipartiteNum G ≤ X.card) : False :=
    never X ⟨col,le_antisymm (size_bip G col) b⟩ mem
  constructor
  · apply Nat.le_of_not_lt
    intro few
    obtain ⟨X,col,mem,b⟩ := swap_in G w C D ic id dis wc wd (by omega)
    exact no X col mem (by omega)
  · apply Nat.le_of_not_lt
    intro few
    obtain ⟨X,col,mem,b⟩ := swap_in G w D C id ic dis.symm wd wc (by omega)
    exact no X col mem (by omega)

theorem occurs_low_degree [DecidableRel G.Adj] (w : V) (small : G.degree w≤3) :
    ∃ X, MaxSet G X ∧ w∈X := by
  classical
  by_contra! never
  obtain ⟨X,⟨C,D,dis,rfl,ic,id⟩,top⟩ := optB G
  rw [card_union_of_disjoint dis] at top
  obtain ⟨c,d⟩ := excluded_colors G w never C D ic id dis top
  have both : C ∩ G.neighborFinset w ∪ D ∩ G.neighborFinset w ⊆ G.neighborFinset w :=
    union_subset inter_subset_right inter_subset_right
  have size := card_le_card both
  rw [card_union_of_disjoint (dis.mono inter_subset_left inter_subset_left),card_neighborFinset_eq_degree] at size
  omega

omit [Fintype V] in
/-- Colors assigned by root-distance parity work on any vertex set with
no edge inside a single distance layer. -/
theorem by_layers (hc : G.Connected) (r : V) (S : Finset V)
    (ok : ∀ u∈S, ∀ v∈S, G.Adj u v → G.dist u r≠G.dist v r) :
    TwoColor G S := by
  classical
  let C := S.filter (fun v => G.dist v r%2=0)
  let D := S.filter (fun v => G.dist v r%2=1)
  have cross (u v : V) (a : u∈S) (b : v∈S) (e : G.Adj u v) : G.dist u r%2 ≠ G.dist v r%2 := by
    have t := hc.dist_triangle (u:=u) (v:=v) (w:=r)
    have q := hc.dist_triangle (u:=v) (v:=u) (w:=r)
    rw [dist_eq_one_iff_adj.mpr e] at t
    rw [dist_eq_one_iff_adj.mpr e.symm] at q
    have := ok u a v b e
    omega
  refine ⟨C,D,disjoint_left.mpr (fun _ a b => by have := (mem_filter.mp a).2; have := (mem_filter.mp b).2; omega),?_,?_,?_⟩
  · ext v
    simp only [C,D,mem_union,mem_filter]
    have part : G.dist v r%2=0 ∨ G.dist v r%2=1 := by omega
    tauto
  all_goals
    intro u hu v hv _ e
    exact cross _ _ (mem_filter.mp hu).1 (mem_filter.mp hv).1 e ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)

#print axioms retained_iff
#print axioms sink_deletion
#print axioms excluded_colors
#print axioms occurs_low_degree
#print axioms by_layers
end Minimal180
