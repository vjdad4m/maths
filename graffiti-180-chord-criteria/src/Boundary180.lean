import StarExchange180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
/-- The range of the attachment heights determines when an ear preserves
every old distance to the specified root. -/
theorem ear_isometric_iff (hc : G.Connected) (N : Finset V) (r k : V)
    (kn : k∈N) (low : ∀ v∈N, G.dist k r ≤ G.dist v r) :
    (∀ v, (ear G N).dist (.inl v) (.inl r)=G.dist v r) ↔
    ∀ v∈N, G.dist v r ≤ G.dist k r+2 := by
  classical
  let H := ear G N
  let z : V ⊕ Unit := .inr ()
  let h := G.dist k r
  have con := ear_connected G hc N ⟨k,kn⟩
  have lip {W : Type u} {J : SimpleGraph W} (jc : J.Connected) {a b s : W} (ab : J.Adj a b) :
      J.dist a s ≤ J.dist b s+1 := by
    have t := jc.dist_triangle (u:=a) (v:=b) (w:=s)
    rw [dist_eq_one_iff_adj.mpr ab] at t
    omega
  constructor
  · intro eq v vn
    have a := lip con (s:=Sum.inl r) (show H.Adj (.inl v) z from vn)
    have b := lip con (s:=Sum.inl r) (show H.Adj z (.inl k) from kn)
    rw [eq v] at a
    rw [eq k] at b
    omega
  · intro high
    let d : V ⊕ Unit → ℕ := Sum.elim (fun a => G.dist a r) (fun _ => h+1)
    obtain ⟨_,eq⟩ := layers H (.inl r) d G.dist_self (fun {a b} e => by
      rcases a with a|a <;> rcases b with b|b
      · exact lip hc e
      · exact high a e
      · exact Nat.add_le_add_right (low b e) 1
      · exact e.elim) (fun v ne => by
      rcases v with a|a
      · obtain ⟨w,e,dd⟩ := Graffiti169.exists_predecessor G hc r a (fun h => ne (congrArg Sum.inl h))
        exact ⟨.inl w,e,dd⟩
      · exact ⟨.inl k,kn,rfl⟩)
    exact fun v => eq (.inl v)

theorem twins_preserve (hc : G.Connected) [DecidableRel G.Adj] (r y : V) :
    ∀ v, (ear G (insert y (G.neighborFinset y))).dist (.inl v) (.inl r)=G.dist v r := by
  classical
  let N := insert y (G.neighborFinset y)
  obtain ⟨k,kn,low⟩ := exists_min_image N (fun a => G.dist a r) (insert_nonempty _ _)
  apply (ear_isometric_iff G hc N r k kn low).mpr
  have near (v : V) (vn : v∈N) : G.dist v y ≤ 1 := by
    rcases mem_insert.mp vn with eq|e
    · rw [eq,dist_self]; omega
    · exact (dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp e).symm).le
  intro v vn
  have a := hc.dist_triangle (u:=v) (v:=y) (w:=r)
  have b := hc.dist_triangle (u:=y) (v:=k) (w:=r)
  have p := near v vn
  have q := near k kn
  rw [dist_comm (u:=k) (v:=y)] at q
  omega

/-- In a sharp state, suppose deleting the eligible endpoint retains the
old parity and that endpoint belongs to exactly one of the two sets.
If a neighbor has degree at least two and zero cost on erasure in the
smaller graph, *either* every next incident triangle gains a bipartite
vertex *or* the smaller rooted instance itself produces a counterexample. -/
theorem boundary_or_counter (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V)
    (r : V) (odd : Bool) (A : Finset (V ⊕ Unit)) (ai : Indep (ear G N) A)
    (par : pull Sum.inl (parity (ear G N) (.inl r) odd)=parity G r odd)
    (once : let P := parity (ear G N) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let P := parity (ear G N) (.inl r) odd
             weightedLeaves (ear G N) (eligible A P (.inl r))+bipartiteNum (ear G N)=1+A.card+P.card)
    (boundary : let U := eligible (pull Sum.inl A) (parity G r odd) r
                ∃ y∈N, (∃ a b, G.Adj y a ∧ G.Adj y b ∧ a≠b) ∧
                  weightedLeaves G (U.erase y)=weightedLeaves G U) :
    (∀ w∈N, let H := ear G N
            bipartiteNum (ear H {Sum.inl w,Sum.inr ()})=bipartiteNum H+1) ∨
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
  by_cases old : localBound G r (parity G r odd)
  · left
    intro w wn
    apply rank_grows_of_optimum G hn N r odd A ai par old once tight _ w wn
    obtain ⟨y,yn,deg,eq⟩ := boundary
    obtain ⟨K,ks,kt,opt,ny⟩ := (internal_optimum_iff G hc (by omega) _ y).mpr ⟨deg,eq⟩
    exact ⟨K,ks,kt,opt,y,yn,ny⟩
  · exact Or.inr (of_failed_local G hc (by omega) r odd old)

/-- No external parity-preservation hypothesis is needed for the exact
true-twin specialization. The connected smaller graph may have cut vertices. -/
theorem twin_boundary [DecidableRel G.Adj] (hc : G.Connected) (hn : 2<Fintype.card V)
    (r y : V) (odd : Bool)
    (A : Finset (V ⊕ Unit)) (ai : Indep (ear G (insert y (G.neighborFinset y))) A)
    (once : let P := parity (ear G (insert y (G.neighborFinset y))) (.inl r) odd
            (.inr ()∈A ∨ .inr ()∈P) ∧ ¬(.inr ()∈A ∧ .inr ()∈P))
    (tight : let H := ear G (insert y (G.neighborFinset y))
             let P := parity H (.inl r) odd
             weightedLeaves H (eligible A P (.inl r))+bipartiteNum H=1+A.card+P.card) :
    (∀ w∈insert y (G.neighborFinset y), let H := ear G (insert y (G.neighborFinset y))
      bipartiteNum (ear H {Sum.inl w,Sum.inr ()})=bipartiteNum H+1) ∨
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
  let N := insert y (G.neighborFinset y)
  by_cases old : localBound G r (parity G r odd)
  · left
    intro w wn
    apply rank_grows G hc hn N y (mem_insert_self _ _) (fun v e => mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr e))
      r odd A ai _ old once tight w wn
    ext v
    simp only [mem_pull,mem_parity,twins_preserve G hc r y v,N]
  · exact Or.inr (of_failed_local G hc (by omega) r odd old)

#print axioms ear_isometric_iff
#print axioms twins_preserve
#print axioms boundary_or_counter
#print axioms twin_boundary
end Assembly180
