import BothLargeClose189
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- A finite vertex graph with at least three vertices and no vertex cut of
size below two has minimum degree two. -/
theorem min_two_from_connectivity
    (conn : ∀ R : Finset V, R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (large : 3≤Fintype.card V) (x : V) : 2≤G.degree x := by
  classical
  by_contra! low
  let D := G.neighborFinset x
  have dc : D.card<2 := by simpa [D] using low
  have xn : x∉D := fun h => ((mem_neighborFinset G x x).mp h).ne rfl
  have mate : ∃ y : V,y∉insert x D := by
    by_cases h : ∃ y : V,y∉insert x D
    · exact h
    exfalso
    have sub : (univ : Finset V)⊆insert x D := by
      intro y _
      exact Classical.byContradiction (fun yn => h ⟨y,yn⟩)
    have card := card_le_card sub
    rw [card_univ,card_insert_of_not_mem xn] at card
    omega
  obtain ⟨y,yn⟩ := mate
  have yx : y≠x := fun e => yn (mem_insert.mpr (Or.inl e))
  have yd : y∉D := fun z => yn (mem_insert_of_mem z)
  let W : Set V := ((↑D : Set V)ᶜ)
  let s : W := ⟨x,xn⟩
  let t : W := ⟨y,yd⟩
  have st : s≠t := fun e => yx (congrArg Subtype.val e).symm
  obtain ⟨w⟩ := (conn D dc) s t
  have forward {u v : W} (q : (G.induce W).Walk u v) (eq : u=s) : v=s := by
    cases q with
    | nil => exact eq
    | @cons u z v uz q =>
      subst u
      have xz : G.Adj x z.val := uz
      exact (z.property ((mem_neighborFinset G x z.val).mpr xz)).elim
  exact st (forward w rfl).symm

/-- With exact degree-four hypotheses, a two-component cut whose vertices
have distance at least three suffices for a spanning path. The distance
bound in ActualTwoCut189 makes this precisely the distance-three branch. -/
theorem traceable_at_actual_dist_three_cut (hc : G.Connected) (a b : V) (ab : a≠b)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (conn : ∀ R : Finset V, R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (exactly : 2=Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent)
    (distance : 3≤G.dist a b) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have del (z : V) : (G.induce {x : V | x≠z}).Connected := by
    have eq : ((↑({z} : Finset V) : Set V)ᶜ) = {x : V | x≠z} := by ext x; simp
    have c := conn ({z} : Finset V) (by simp)
    rw [eq] at c
    exact c
  obtain ⟨S⟩ := exists_cut_pair hc a b ab even degree del exactly
  obtain ⟨x,xh,_⟩ := S.hita false
  have xa : x≠a := fun e => (S.off false).1 (e ▸ xh)
  have xb : x≠b := fun e => (S.off false).2 (e ▸ xh)
  have large : 3≤Fintype.card V := by
    have c := card_le_univ ({x,a,b}:Finset V)
    simp [xa,xb,ab] at c
    omega
  exact S.traceable_at_dist_three distance conn (min_two_from_connectivity conn large)

#print axioms traceable_at_actual_dist_three_cut
end Graffiti189LongestPath.TwoCut
