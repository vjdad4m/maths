import RootReserve180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Simultaneously realize both stars when their centers and leaves are disjoint. -/
theorem two_stars (H : SimpleGraph V) (hc : H.Connected) (r t : V) (tr : t≠r) (apart : ¬H.Adj t r)
    (sep : ∀ x,H.Adj r x → ¬H.Adj t x) :
    ∃ K≤H, K.IsTree ∧ (∀ z,H.Adj r z → K.Adj r z) ∧ (∀ z,H.Adj t z → K.Adj t z) := by
  classical
  let tips := H.neighborFinset t
  let p (x : V) := if x∈tips then t else r
  let d (x : V) := if x=r then 0 else if x∈tips then 2 else 1
  have nt : t∉tips := by simp [tips]
  have nr : r∉tips := fun m => apart ((H.mem_neighborFinset _ _).mp m)
  have down (x : V) (xr : x≠r) : d (p x)<d x := by
    by_cases xt : x∈tips <;> simp [p,d,xt,xr,nt,tr]
  obtain ⟨T,tree,edges⟩ := virtual_tree r p d down
  obtain ⟨K,sub,kt,keep⟩ := keep_target H T hc tree
  refine ⟨K,sub,kt,?_,?_⟩
  · intro z rz
    have miss : z∉tips := fun m => sep z rz ((H.mem_neighborFinset _ _).mp m)
    exact keep ⟨rz,(show T.Adj z r by simpa [p,miss] using edges z rz.ne.symm).symm⟩
  · intro z tz
    have mt : z∈tips := (H.mem_neighborFinset _ _).mpr tz
    exact keep ⟨tz,(show T.Adj z t by simpa [p,mt] using edges z (fun eq => nr (eq ▸ mt))).symm⟩

/-- In the odd-root test, a second doubly marked vertex contributes the
branching of its whole star of parity-changing edges, simultaneously with the root. -/
theorem two_star_reserve (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r t : V) (I : Finset V) (ii : Indep G I) (ir : r∈I) (it : t∈I)
    (qt : t∈parity G r true) (dr : 1<G.degree r) :
    let Q := parity G r true
    let H := alternating G Q
    1+I.card+Q.card+(G.degree r-1)+(H.degree t-2)≤weightedLeaves G (eligible I Q r)+Fintype.card V := by
  classical
  intro Q H
  have rq : r∉Q := by simp [Q,mem_parity,dist_self]
  have tr : t≠r := fun e => rq (e ▸ qt)
  obtain ⟨con,star⟩ := alternating_parity G gc r true
  have apart : ¬H.Adj t r := fun e => ii t it r ir tr e.1
  have sep (x : V) (e : H.Adj r x) (z : H.Adj t x) : False :=
    rq (e.2.mpr (z.2.mp qt))
  obtain ⟨K,kh,kt,ks,ktip⟩ := two_stars H con r t tr apart sep
  have kg : K≤G := fun _ _ e => (kh e).1
  have rd : K.degree r=G.degree r := by
    have eq : K.neighborFinset r=G.neighborFinset r := by
      ext x; simp only [mem_neighborFinset]; exact ⟨fun e => kg e,fun e => ks _ (star _ e)⟩
    simpa only [card_neighborFinset_eq_degree] using congrArg card eq
  have td : K.degree t=H.degree t := by
    have eq : K.neighborFinset t=H.neighborFinset t := by
      ext x; simp only [mem_neighborFinset]; exact ⟨fun e => kh e,fun e => ktip _ e⟩
    simpa only [card_neighborFinset_eq_degree] using congrArg card eq
  have internal : r∉leaves K := by
    intro m; have one : K.degree r=1 := (mem_filter.mp m).2; omega
  let X := I∪Q
  let D := X\(I∩Q)
  have id := tree_defect K kt hn r internal I Q (fun x xm y ym ne e => ii x xm y ym ne (kg e)) (fun e => (kh e).2)
  change Fintype.card V+(eligible I Q r∩leaves K).card+(K.edgeFinset∩D.sym2).card=
    1+I.card+Q.card+D.card+∑ v∈X,(K.degree v-2) at id
  have forest := forest_strict K kt D ⟨r,by simp [D,X,ir,rq]⟩
  have xnorm : ({t,r}:Finset V)⊆X := insert_subset (mem_union_left _ it) (singleton_subset_iff.mpr (mem_union_left _ ir))
  have sum := sum_le_sum_of_subset_of_nonneg (f:=fun v => K.degree v-2) xnorm (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert (by simp [tr]),sum_singleton,rd,td] at sum
  have pay : (eligible I Q r∩leaves K).card≤weightedLeaves G (eligible I Q r) :=
    le_sup (f:=fun T => (eligible I Q r∩leaves T).card) (mem_filter.mpr ⟨mem_univ _,kg,kt⟩)
  change (H.degree t-2)+(G.degree r-2)≤∑ v∈X,(K.degree v-2) at sum
  omega

#print axioms two_stars
#print axioms two_star_reserve
end Minimal180.Transversals
