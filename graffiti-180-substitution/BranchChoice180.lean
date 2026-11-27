import DeletionClass180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PortParity
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def CoreTest (G : SimpleGraph V) (N U : Finset V) (t : ℕ) : Prop :=
  ∃ S⊆U,t≤S.card ∧ AllowsLeaves G N S

def PortTest (G : SimpleGraph V) (N U : Finset V) (e : Bool) (t : ℕ) : Prop :=
  ∃ x∈N,t≤weightedLeaves G (U.erase x)+e.toNat

theorem uncredited_core (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (degree : 1<N.card) (t : ℕ) (port : PortTest G N U false t) :
    CoreTest G N U t := by
  have nz : N.Nonempty := card_pos.mp (by omega)
  exact (star_core_score G gc (by omega) N U nz t).mp
    ((old_graph_iff G gc hn N U degree false t).mpr (Or.inr port))

/-- When only the port alternative works, the root is credited, every
optimal port misses the quota by exactly one without that credit, and
the largest feasible first-form quota is exactly the same value. -/
theorem port_only_rigid (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (degree : 1<N.card) (e : Bool) (t : ℕ)
    (port : PortTest G N U e t) (no : ¬CoreTest G N U t) :
    e=true ∧ ∃ x∈N,t=weightedLeaves G (U.erase x)+1 ∧
      (∀ y∈N,weightedLeaves G (U.erase y)≤weightedLeaves G (U.erase x)) ∧
      (∀ k,CoreTest G N U k ↔ k≤weightedLeaves G (U.erase x)) := by
  classical
  obtain ⟨x,xn,good⟩ := port
  have fail (y : V) (yn : y∈N) : weightedLeaves G (U.erase y)<t := by
    by_contra! pos
    apply no (uncredited_core G gc hn N U degree t _)
    exact ⟨y,yn,by simpa using pos⟩
  have lower := fail x xn
  cases e
  · simp at good; omega
  · simp at good
    have eq : t=weightedLeaves G (U.erase x)+1 := by omega
    refine ⟨rfl,x,xn,eq,fun y yn => by have := fail y yn; omega,?_⟩
    intro k
    constructor
    · rintro ⟨S,inc,cap,allow⟩
      by_contra! large
      exact no ⟨S,inc,by omega,allow⟩
    · intro ok
      exact uncredited_core G gc hn N U degree k ⟨x,xn,by simpa using ok⟩

/-- The two Boolean outcomes for a specific legal marking in the exact
root-deletion criterion. -/
noncomputable def testsFor (G : SimpleGraph V) (N : Finset V) (nz : N.Nonempty) (A : Finset V) (a p : Bool) :
    Prop × Prop :=
  let P := nearParity G N nz (!p)
  let U := A∪P
  let t := 1+A.card+a.toNat+P.card+(!p).toNat-restoredB G N
  (CoreTest G N U t,PortTest G N U (a && !p) t)

private theorem complete_bip (H : SimpleGraph V) (all : ∀ v,Universal H v) (hn : 1<Fintype.card V) :
    bipartiteNum H=2 := by
  classical
  obtain ⟨_,⟨C,D,dis,rfl,ci,di⟩,opt⟩ := optB H
  have small {A : Finset V} (i : Indep H A) : A.card≤1 :=
    card_le_one.mpr (fun x xm y ym => by by_contra n; exact i x xm y ym n (all y x n))
  have l := small ci
  have r := small di
  rw [card_union_of_disjoint dis] at opt
  have low := basic_bipartite H hn
  omega

/-- Every complete restored graph of order at least four forces both
orientations of the disjunction at the same root, on two legal markings.
With only the root independent and even parity the port alternative is
essential. With one old vertex independent and odd parity the core
alternative is essential. The restored graph satisfies ordinary #180. -/
theorem complete_requires_both (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (all : ∀ v,Universal G v) (v : V) :
    let N : Finset V := univ
    let nz : N.Nonempty := ⟨v,mem_univ _⟩
    let even := testsFor G N nz ∅ true false
    let odd := testsFor G N nz {v} false true
    (¬even.1 ∧ even.2) ∧ (odd.1 ∧ ¬odd.2) ∧
      1+independence (ear G N)+Graffiti318.maxEven (ear G N)≤maxLeaves (ear G N)+bipartiteNum (ear G N) := by
  classical
  intro N nz even odd
  have degree : 1<N.card := by simp [N]; omega
  have hu : ∀ y,Universal (ear G N) y := by
    rintro (y|⟨⟩) (x|⟨⟩) ne
    · exact all y x (fun eq => ne (congrArg Sum.inl eq))
    · exact mem_univ _
    · exact mem_univ _
    · exact (ne rfl).elim
  have order : 1<Fintype.card (V⊕Unit) := by simp [Fintype.card_sum]; omega
  have b : restoredB G N=2 := (restored_bipartite ..).symm.trans (complete_bip _ hu order)
  have zero (x : V) : near G N nz x=0 := by
    have h : near G N nz x≤G.dist x x := inf'_le _ (mem_univ x)
    rw [dist_self] at h; omega
  have po : nearParity G N nz true=∅ := by ext x; simp [nearParity,zero]
  have pe : nearParity G N nz false=univ := by ext x; simp [nearParity,zero]
  have ev : even=(CoreTest G N ∅ 1,PortTest G N ∅ true 1) := by simp [even,testsFor,po,b]
  have od : odd=(CoreTest G N univ (Fintype.card V),PortTest G N univ false (Fintype.card V)) := by
    have full : ({v}:Finset V)∪univ=univ := union_eq_right.mpr (subset_univ _)
    simp [odd,testsFor,pe,b,full]
  have passes (p : Bool) : Passes G N degree p :=
    port_dominates_passes G gc hn N degree v (mem_univ _) (fun x h => (h (mem_univ x)).elim) p
  have ed : even.1 ∨ even.2 := passes false ∅ true (by simp [Indep]) (by simp)
  have odj : odd.1 ∨ odd.2 := passes true {v} false (by simp [Indep]) (by simp)
  rw [ev] at ed ⊢
  rw [od] at odj ⊢
  have first : ¬CoreTest G N ∅ 1 := by
    rintro ⟨S,sub,le,_⟩
    have eq : S=∅ := Subset.antisymm sub (empty_subset _)
    simp [eq] at le
  have second : ¬PortTest G N univ false (Fintype.card V) := by
    rintro ⟨x,_,score⟩
    obtain ⟨K,_,_,eq⟩ := tree_opt G gc (univ.erase x)
    have cap : ((univ.erase x)∩leaves K).card≤(univ.erase x).card := card_le_card inter_subset_left
    rw [eq,card_erase_of_mem (mem_univ x),card_univ] at cap
    simp at score; omega
  exact ⟨⟨first,ed.resolve_left first⟩,⟨odj.resolve_right second,second⟩,
    ordinary_of_rooted _ (ear_connected G gc N nz) (fun r p => universal_root _ (ear_connected G gc N nz) order r (hu r) p)⟩

#print axioms uncredited_core
#print axioms port_only_rigid
#print axioms complete_requires_both
end Minimal180.Substitution
