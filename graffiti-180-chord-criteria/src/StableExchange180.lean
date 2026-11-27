import SeriesPair180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A nonroot vertex counted on both sides of the independent/parity
overlap has a predecessor in neither set. This remains visible downstairs
when deletion preserves the parity of the surviving vertices. -/
theorem free_parent (hc : G.Connected) (N : Finset V) (nz : N.Nonempty)
    (r : V) (odd : Bool) (A : Finset V)
    (ai : Indep (ear G N) (lift A true))
    (par : parity (ear G N) (.inl r) odd=lift (parity G r odd) true) :
    ∃ x∈N, x∉eligible A (parity G r odd) r := by
  let H := ear G N
  let z : V ⊕ Unit := .inr ()
  let s : V ⊕ Unit := .inl r
  have nzr : z≠s := fun h => Sum.noConfusion h
  obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor H (ear_connected G hc N nz) s z nzr
  rcases w with x|t
  · refine ⟨x,e,?_⟩
    intro xu
    rcases (eligible_iff.mp xu).1 with inA|inP
    · exact ai z (by simp [z]) (.inl x) ((inl_lift ..).mpr inA) (fun h => Sum.noConfusion h) e
    · have zP : z∈parity H s odd := by change z∈parity (ear G N) (.inl r) odd; rw [par]; simp [z]
      have xP : Sum.inl x∈parity H s odd := by change Sum.inl x∈parity (ear G N) (.inl r) odd; rw [par]; exact (inl_lift ..).mpr inP
      have zd := (mem_parity H s z odd).mp zP
      have xd := (mem_parity H s (.inl x) odd).mp xP
      omega
  · exact e.elim

/-- For every stable nonroot deletion the two invariant gains cover all
but at most one unit of the deleted memberships, including double marks. -/
theorem stable_budget (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V) (nz : N.Nonempty)
    (r : V) (odd a p : Bool) (A : Finset V)
    (ai : Indep (ear G N) (lift A a))
    (par : parity (ear G N) (.inl r) odd=lift (parity G r odd) p) :
    weightedLeaves G (eligible A (parity G r odd) r)+a.toNat+p.toNat ≤
      weightedLeaves (ear G N) (eligible (lift A a) (parity (ear G N) (.inl r) odd) (.inl r))+1 := by
  let U := eligible A (parity G r odd) r
  rw [par,eligible_lift]
  by_cases both : a=true ∧ p=true
  · obtain ⟨rfl,rfl⟩ := both
    obtain ⟨w,wn,out⟩ := free_parent G hc N nz r odd A ai par
    have h := attach G hc hn N U true w wn
    rw [erase_eq_of_not_mem out] at h
    change weightedLeaves G U+1+1≤weightedLeaves (ear G N) (lift U true)+1
    change weightedLeaves G U+1≤weightedLeaves (ear G N) (lift U true) at h
    exact Nat.add_le_add_right h 1
  · obtain ⟨w,wn⟩ := nz
    have h := attach G hc hn N U (a||p) w wn
    have c := erase_cost G U w
    have mass : a.toNat+p.toNat=(a||p).toNat := by cases a <;> cases p <;> simp_all
    change weightedLeaves G U+a.toNat+p.toNat≤weightedLeaves (ear G N) (lift U (a||p))+1
    omega

/-- Every parity-stable deletion of a minimum failed rooted instance
is tight with its inherited independent set. The new graph misses by
one, and the two graphs have equal maximum induced bipartite order. -/
theorem failed_stable (hc : G.Connected) (hn : 2<Fintype.card V) (N : Finset V) (nz : N.Nonempty)
    (r : V) (odd a p : Bool) (A : Finset V)
    (ai : Indep (ear G N) (lift A a))
    (par : parity (ear G N) (.inl r) odd=lift (parity G r odd) p)
    (old : localBound G r (parity G r odd))
    (bad : let H := ear G N
           let P := parity H (.inl r) odd
           let B := lift A a
           weightedLeaves H (eligible B P (.inl r))+bipartiteNum H < 1+B.card+P.card) :
    let C := parity G r odd
    let H := ear G N
    let P := parity H (.inl r) odd
    let B := lift A a
    weightedLeaves G (eligible A C r)+bipartiteNum G=1+A.card+C.card ∧
    weightedLeaves H (eligible B P (.inl r))+bipartiteNum H=B.card+P.card ∧
    bipartiteNum H=bipartiteNum G ∧
    ∀ D, Indep G D → eligible D C r=eligible A C r → D.card≤A.card := by
  dsimp only at *
  have h := stable_budget G hc hn N nz r odd a p A ai par
  have rank := rank_mono G N
  have ind : Indep G A := fun x hx y hy ne e => ai _ ((inl_lift ..).mpr hx) _
    ((inl_lift ..).mpr hy) (fun eq => ne (Sum.inl.inj eq)) e
  have base := old A ind
  have ct := congrArg card par
  rw [card_lift] at ct
  rw [card_lift] at bad ⊢
  refine ⟨by omega,by omega,by omega,?_⟩
  intro D di same
  have alt := old D di
  rw [same] at alt
  omega

omit [Fintype V] in
theorem eligible_insert {A P : Finset V} {x r : V} (xp : x∈P) (xr : x≠r) :
    eligible (insert x A) P r=eligible A P r := by
  ext v
  simp only [eligible_iff,mem_insert]
  have neq := xr.symm
  by_cases vx : v=x
  · subst v; tauto
  · tauto

omit [Fintype V] in
/-- In a smaller tight graph, every nonroot vertex of the tested parity
outside A has an A-neighbor. This allows the independent set downstairs
to change, with the eligibility signature fixed. -/
theorem tight_domination (r : V) (P A : Finset V) (ai : Indep G A)
    (optimal : ∀ D, Indep G D → eligible D P r=eligible A P r → D.card≤A.card)
    (x : V) (xp : x∈P) (xr : x≠r) (xa : x∉A) : ∃ y∈A, G.Adj x y := by
  classical
  by_contra! no
  have plus : Indep G (insert x A) := by
    intro u hu v hv ne e
    rcases mem_insert.mp hu with rfl|a <;> rcases mem_insert.mp hv with rfl|b
    · exact ne rfl
    · exact no v b e
    · exact no u a e.symm
    · exact ai u a v b ne e
  have b := optimal _ plus (eligible_insert xp xr)
  rw [card_insert_of_not_mem xa] at b
  omega

#print axioms free_parent
#print axioms stable_budget
#print axioms failed_stable
#print axioms eligible_insert
#print axioms tight_domination
end Minimal180
