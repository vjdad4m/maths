import DiagonalPhaseHost

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.DiagonalPhaseFixture
open RemoteSpacedPrismHandle (Port)
open SquareCap (boundary HasFactor)

def mate (k : Bool) (v : Core) : Core :=
  (if k then [11,2,1,4,3,6,5,8,7,10,9,0,18,19,20,23,22,21,12,13,14,17,16,15] else [1,0,3,2,5,4,7,6,9,8,11,10,18,19,20,23,22,21,12,13,14,17,16,15] : List Core)[v.val]!
theorem mate_involutive (k : Bool) : Function.Involutive (mate k) := by
  change ∀ v : Core,mate k (mate k v)=v
  cases k <;> decide
theorem mate_adjacent : ∀ k (v : Core),core.Adj v (mate k v) := by decide
theorem no_charges : ∀ k i,mate k (a i)≠b i := by decide

def rank (k : Bool) : SimpleGraph Board where
  Adj x y := board.Adj x y ∧ match x,y with
    | .inl u,.inl v => mate k u≠v
    | _,_ => True
  symm := by
    rintro (x|i) (y|j) h
    · exact ⟨h.1.symm,fun e=>h.2 (by rw [←e,mate_involutive])⟩
    all_goals exact ⟨h.1.symm,trivial⟩
  loopless x h := board.loopless x h.1

instance (k : Bool) : DecidableRel (rank k).Adj := by
  rintro (x|i) (y|j)
  all_goals change Decidable (_ ∧ _)
  all_goals infer_instance

def pairUnion : SimpleGraph Board := rank false ⊔ rank true
instance : DecidableRel pairUnion.Adj := by
  intro x y
  change Decidable ((rank false).Adj x y ∨ (rank true).Adj x y)
  infer_instance

theorem pair_le : pairUnion ≤ board := by
  intro x y h
  change (rank false).Adj x y ∨ (rank true).Adj x y at h
  exact h.elim (·.1) (·.1)

def Closed (G : SimpleGraph Board) (s : Finset Board) : Prop :=
  ∀ x y : Board,x∈s → G.Adj x y → y∈s
instance (G : SimpleGraph Board) [DecidableRel G.Adj] (s : Finset Board) : Decidable (Closed G s) := by
  unfold Closed
  infer_instance

private theorem no_factor_closed_mod (G : SimpleGraph Board) {S : Finset Board}
    (closed : Closed G S) (size : S.card%3≠0) : ¬HasFactor G := by
  classical
  rintro ⟨P,tiles',disj,cover⟩
  let Q := P.filter (fun T => ∃ v∈T,v∈S)
  have inside (T : Finset Board) (ht : T∈P) (inter : ∃ v∈T,v∈S) : T ⊆ S := by
    obtain ⟨_,c,hc,adj⟩ := tiles' T ht
    obtain ⟨v,hv,vs⟩ := inter
    have cs : c∈S := by
      by_cases e : v=c
      · exact e ▸ vs
      · exact closed v c vs (adj v hv e).symm
    intro y hy
    by_cases e : y=c
    · exact e.symm ▸ cs
    · exact closed c y cs (adj y hy e)
  have eq : Q.biUnion id = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨T,tq,xt⟩ := mem_biUnion.mp hx
      obtain ⟨ht,h⟩ := mem_filter.mp tq
      exact inside T ht h xt
    · intro hx
      have xP : x∈P.biUnion id := by rw [cover]; exact mem_univ _
      obtain ⟨T,ht,xt⟩ := mem_biUnion.mp xP
      exact mem_biUnion.mpr ⟨T,mem_filter.mpr ⟨ht,x,xt,hx⟩,xt⟩
  have card : (Q.biUnion id).card = ∑ T∈Q,T.card := by
    apply card_biUnion
    intro A ha B hb ne
    exact disj A (mem_filter.mp ha).1 B (mem_filter.mp hb).1 ne
  rw [eq] at card
  have cc : (∑ T∈Q,T.card) = Q.card * 3 := by
    rw [show (∑ T∈Q,T.card) = ∑ _T∈Q,(3:ℕ) from
      sum_congr rfl (fun T ht => (tiles' T (mem_filter.mp ht).1).1)]
    simp
  omega

def square : Finset Core := {0,5,6,11}
def squareSides : List (Core×Core) := [(0,6),(6,5),(5,11),(11,0)]
def exchange : List (Core×Core) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,0)]
def spokes : Finset (Core×Core) := {(0,1),(5,4),(6,7),(11,10)}

set_option maxRecDepth 10000 in
theorem boundary_exact :
    boundary core (fun x => decide (x∈square)) = spokes := by
  ext e
  have tab : ∀ e : Core×Core,(e.1∈square ∧ e.2∉square ∧ core.Adj e.1 e.2) ↔
      e∈spokes := by decide
  simpa [boundary] using tab e

set_option maxRecDepth 10000 in
theorem induced_unmarked_square :
    (∀ x y : Core,x∈square → y∈square →
      (core.Adj x y ↔ (x,y)∈squareSides ∨ (y,x)∈squareSides)) ∧
    (∀ i : Port,a i∉square ∧ b i∉square) := by decide

set_option maxRecDepth 10000 in
theorem release_exact :
    (∀ e∈spokes,mate false e.1=e.2 ∧ mate true e.1≠e.2) ∧
    (∀ x y : Core,((mate false x=y ∧ mate true x≠y) ∨
      (mate true x=y ∧ mate false x≠y)) ↔ (x,y)∈exchange∨(y,x)∈exchange) := by decide

def closedP : Finset Board := (route [0,5,6,11]).toFinset
def closedQ : Finset Board := (route [4,5,10,11,24]).toFinset

set_option maxRecDepth 10000 in
theorem bad_shores :
    (closedP.card=4 ∧ Closed (rank false) closedP) ∧
    (closedQ.card=5 ∧ Closed (rank true) closedQ) := by decide

theorem rank_fails (k : Bool) : ¬HasFactor (rank k) := by
  cases k
  · apply no_factor_closed_mod _ bad_shores.1.2
    rw [bad_shores.1.1]
    decide
  · apply no_factor_closed_mod _ bad_shores.2.2
    rw [bad_shores.2.1]
    decide

#print axioms no_charges
#print axioms release_exact
#print axioms rank_fails
end KelmansCactus.AtomicBridge.DiagonalPhaseFixture
