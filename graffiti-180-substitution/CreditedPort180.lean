import BranchChoice180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PortParity
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- When the new root receives the leaf credit, no old port can be
independent-marked or parity-marked. Every port therefore has the
same deletion score and erasing it from the old mark changes nothing. -/
theorem credited_erases (G : SimpleGraph V) (N A : Finset V) (nz : N.Nonempty)
    (a p : Bool) (valid : a=true → Disjoint A N) (credit : (a && !p)=true) :
    ∀ x∈N,(A∪nearParity G N nz (!p)).erase x=A∪nearParity G N nz (!p) := by
  classical
  have bits : a=true ∧ p=false := by cases a <;> cases p <;> simp_all
  obtain ⟨rfl,rfl⟩ := bits
  intro x xn
  apply erase_eq_of_not_mem
  intro hit
  have zero : near G N nz x=0 := by
    have le : near G N nz x≤G.dist x x := inf'_le _ xn
    rw [dist_self] at le; omega
  rcases mem_union.mp hit with xa|xp
  · exact disjoint_left.mp (valid rfl) xa xn
  · simp [nearParity,zero] at xp

/-- Normal form for a single legal marking, on the old graph alone.
The extra case has no existential port and no marked-port erasure. -/
theorem mark_normal (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N A : Finset V) (degree : 1<N.card) (a p : Bool) (valid : a=true → Disjoint A N) (t : ℕ) :
    let nz : N.Nonempty := card_pos.mp (by omega)
    let U := A∪nearParity G N nz (!p)
    CoreTest G N U t ∨ PortTest G N U (a && !p) t ↔
      CoreTest G N U t ∨ (a=true ∧ p=false ∧ t=weightedLeaves G U+1 ∧
        ∀ k,CoreTest G N U k ↔ k≤weightedLeaves G U) := by
  classical
  intro nz U
  constructor
  · rintro (core|port)
    · exact Or.inl core
    by_cases ok : CoreTest G N U t
    · exact Or.inl ok
    obtain ⟨credit,x,xn,eq,_,maximal⟩ := port_only_rigid G gc hn N U degree _ t port ok
    have off : U.erase x=U := credited_erases G N A nz a p valid credit x xn
    rw [off] at eq maximal
    have bits : a=true ∧ p=false := by cases a <;> cases p <;> simp_all
    exact Or.inr ⟨bits.1,bits.2,eq,maximal⟩
  · rintro (core|⟨aa,pp,eq,_⟩)
    · exact Or.inl core
    obtain ⟨x,xn⟩ := nz
    have credit : (a && !p)=true := by simp [aa,pp]
    have off : U.erase x=U := credited_erases G N A _ a p valid credit x xn
    exact Or.inr ⟨x,xn,by rw [off,credit,eq]; simp⟩

/-- For odd root parity (and for any uncredited independent marking)
the core alternative is the exact sole test. For even parity, all
additional successful markings have the single exceptional form above. -/
theorem deleted_root_normal (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (degree : 1<N.card) (p : Bool) :
    let nz : N.Nonempty := card_pos.mp (by omega)
    let P := nearParity G N nz (!p)
    localBound (ear G N) (.inr ()) (parity (ear G N) (.inr ()) p) ↔
      ∀ A : Finset V, ∀ a : Bool, Indep G A → (a=true → Disjoint A N) →
        let U := A∪P
        let t := 1+A.card+a.toNat+P.card+(!p).toNat-restoredB G N
        CoreTest G N U t ∨ (a=true ∧ p=false ∧ t=weightedLeaves G U+1 ∧
          ∀ k,CoreTest G N U k ↔ k≤weightedLeaves G U) := by
  intro nz P
  constructor
  · intro bound A a ai valid
    exact (mark_normal G gc hn N A degree a p valid _).mp ((deleted_root_iff G gc hn N degree p).mp bound A a ai valid)
  · intro tests
    apply (deleted_root_iff G gc hn N degree p).mpr
    intro A a ai valid
    exact (mark_normal G gc hn N A degree a p valid _).mpr (tests A a ai valid)

/-- In odd parity the entire rooted inequality is equivalent to finding
a feasible old core for every legal independent marking. -/
theorem odd_root_core_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (degree : 1<N.card) :
    let nz : N.Nonempty := card_pos.mp (by omega)
    let P := nearParity G N nz false
    localBound (ear G N) (.inr ()) (parity (ear G N) (.inr ()) true) ↔
      ∀ A : Finset V, ∀ a : Bool, Indep G A → (a=true → Disjoint A N) →
        CoreTest G N (A∪P) (1+A.card+a.toNat+P.card-restoredB G N) := by
  simpa using deleted_root_normal G gc hn N degree true

#print axioms credited_erases
#print axioms mark_normal
#print axioms deleted_root_normal
#print axioms odd_root_core_iff
end Minimal180.Substitution
