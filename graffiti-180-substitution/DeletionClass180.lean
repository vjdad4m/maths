import Substitution180
import DeletedRoot180
import RankTwoAssembly180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 PortParity
open Classical
universe u

/-- A certificate may use previously verified rank-two assemblies, dominating
edges at every root, covered substitutions, and further one-vertex sums. -/
inductive Family : {V : Type u} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop where
  | prior {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
      (old : RootEar.RankTwoFamily G) : Family G
  | edges {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
      (hc : G.Connected) (hn : 1<Fintype.card V) (all : ∀ r,∃ y,DomEdge G r y) : Family G
  | expand {V B : Type u} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
      {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} (h : Bags H G f) (cover : CoversBags H G f)
      (gc : G.Connected) (hn : 1<Fintype.card B) (old : Family G) : Family H
  | split {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {c : V} {S T : Finset V}
      (gc : G.Connected) (cut : Split G c S T) (left : Family (side G S)) (right : Family (side G T)) : Family G

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem Family.rooted (proof : Family G) : ∀ r p,localBound G r (parity G r p) := by
  induction proof with
  | prior old => exact old.rooted
  | edges hc hn all =>
    intro r p
    obtain ⟨_,e⟩ := all r
    exact dom_edge_rooted _ hc hn e p
  | expand h cov gc hn _ ih => exact fun r p => h.rooted cov gc hn r p (ih _ _)
  | split gc s _ _ l r =>
    intro v p
    rcases s.either v with vs|vt
    · exact s.parity_join gc ⟨v,vs⟩ p l r
    · exact s.flip.parity_join gc ⟨v,vt⟩ p r l

theorem ordinary_of_rooted (G : SimpleGraph V) (hc : G.Connected)
    (ok : ∀ r p,localBound G r (parity G r p)) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  haveI : Nonempty V := hc.nonempty
  obtain ⟨r,_,re⟩ := exists_mem_eq_sup (s:=univ) (f:=evenCount G) univ_nonempty
  obtain ⟨A,ha,ae⟩ := exists_mem_eq_sup (s:=univ.filter (Indep G)) (f:=card)
    ⟨∅,mem_filter.mpr ⟨mem_univ _,by simp [Indep]⟩⟩
  have bd := ok r false A (mem_filter.mp ha).2
  have le : weightedLeaves G (eligible A (parity G r false) r)≤maxLeaves G := by
    rw [←weighted_all]
    exact (restrict_leaves G _ univ).trans (by simp)
  change maxEven G=evenCount G r at re
  change independence G=A.card at ae
  rw [re,ae,even_equiv]
  omega

theorem Family.ordinary (proof : Family G) : 1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  apply ordinary_of_rooted G _ proof.rooted
  cases proof with
  | prior old => cases old <;> assumption
  | edges hc _ _ => exact hc
  | expand h _ gc hn _ => exact h.connected gc hn
  | split gc _ _ _ => exact gc

/-- The threshold and the two alternatives involve the deleted graph only. -/
def Passes (G : SimpleGraph V) (N : Finset V) (degree : 1<N.card) (p : Bool) : Prop :=
  let nz : N.Nonempty := card_pos.mp (by omega)
  let P := nearParity G N nz (!p)
  ∀ A : Finset V, ∀ a : Bool, Indep G A → (a=true → Disjoint A N) →
    let U := A∪P
    let t := 1+A.card+a.toNat+P.card+(!p).toNat-restoredB G N
    (∃ S⊆U,t≤S.card ∧ AllowsLeaves G N S) ∨
    ∃ x∈N,t≤weightedLeaves G (U.erase x)+(a && !p).toNat

theorem family_passes (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (degree : 1<N.card) (proof : Family (ear G N)) (p : Bool) : Passes G N degree p :=
  (deleted_root_iff G gc hn N degree p).mp (proof.rooted _ _)

/-- Checkable on the deleted graph: one port dominates every nonport. -/
theorem port_dominates_passes (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (degree : 1<N.card) (y : V) (yn : y∈N) (cov : ∀ x∉N,G.Adj x y)
    (p : Bool) : Passes G N degree p := by
  classical
  have e : DomEdge (ear G N) (.inr ()) (.inl y) := by
    refine ⟨yn,?_⟩
    rintro (x|⟨⟩) nr _
    · by_cases xn : x∈N
      · exact Or.inl xn
      · exact Or.inr (cov x xn)
    · exact (nr rfl).elim
  apply (deleted_root_iff G gc hn N degree p).mp
  exact dom_edge_rooted _ (ear_connected G gc N ⟨y,yn⟩) (by simp [Fintype.card_sum]; omega) e p

variable {B : Type*} [Fintype B] [DecidableEq B] {J : SimpleGraph B}

/-- No restrictions are imposed on the nonempty bags. -/
theorem bipartite_substitution_ordinary {H : SimpleGraph V} {f : V→B} (h : Bags H J f)
    (jc : J.Connected) (ord : 1<Fintype.card B) (bi : TwoColor J univ) :
    1+independence H+maxEven H≤maxLeaves H+bipartiteNum H :=
  ordinary_of_rooted H (h.connected jc ord) (h.bipartiteRooted jc ord bi)

theorem bipartite_substitution_passes (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N : Finset V) (degree : 1<N.card) {f : V⊕Unit→B} (h : Bags (ear G N) J f)
    (jc : J.Connected) (ord : 1<Fintype.card B) (bi : TwoColor J univ) (p : Bool) : Passes G N degree p :=
  (deleted_root_iff G gc hn N degree p).mp (h.bipartiteRooted jc ord bi _ _)

#print axioms Family.rooted
#print axioms ordinary_of_rooted
#print axioms Family.ordinary
#print axioms family_passes
#print axioms port_dominates_passes
#print axioms bipartite_substitution_ordinary
#print axioms bipartite_substitution_passes
end Minimal180.Substitution
