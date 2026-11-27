import RemoteSpacedPrismLayout
import RemoteCutCertificate
import RemoteSpacedPrismWidth
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Chain

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.DiagonalReleaseFixture
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide ThreeConnected boundary HasFactor FactorOn IsTile)

abbrev Core := Fin 18

def edgeTable : RemoteCutCertificate.Table 18 where
  edges := [(0, 1), (0, 3), (0, 4), (1, 2), (1, 8), (2, 3), (2, 5), (3, 9), (4, 5), (4, 7), (5, 6), (6, 7), (6, 13), (7, 14), (8, 9), (8, 11), (9, 10), (10, 11), (10, 16), (11, 17), (12, 13), (12, 15), (12, 17), (13, 14), (14, 15), (15, 16), (16, 17)]
  sorted := by decide
  nodup := by decide

abbrev core : SimpleGraph Core := edgeTable.graph

theorem core_cube : ∀ v,core.degree v=3 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem cut_valid :
    edgeTable.cert 4 1 [1,0,2,3,9,4,5,6,7,10,11,13,14,12,15,16,17]
      (RemoteCutCertificate.Table.base 8)=true := by decide

theorem core_cyclic_four : SmallTrivial core := edgeTable.cyclic_four cut_valid

def a : Port → Core
  | .inl (.inl false) => 6
  | .inl (.inl true) => 7
  | .inl (.inr false) => 10
  | .inl (.inr true) => 11
  | .inr false => 4
  | .inr true => 8

def b : Port → Core
  | .inl (.inl false) => 13
  | .inl (.inl true) => 14
  | .inl (.inr false) => 16
  | .inl (.inr true) => 17
  | .inr false => 5
  | .inr true => 9

def marks : Marks core Port where
  a := a
  b := b
  edge := by decide
  separated := by
    intro i j x
    have h : ∀ i j : Port, ∀ x : Core, x=a i∨x=b i → x=a j∨x=b j → i=j := by decide
    exact h i j x

abbrev board := marks.expanded


abbrev Board := Core ⊕ Port

instance : DecidableRel board.Adj := by
  intro x y
  rcases x with (x|i) <;> rcases y with (y|j)
  · change Decidable (core.Adj x y ∧ ¬∃ i : Port, (x=a i ∧ y=b i) ∨ (x=b i ∧ y=a i))
    infer_instance
  · change Decidable (x=a j ∨ x=b j); infer_instance
  · change Decidable (y=a i ∨ y=b i); infer_instance
  · change Decidable False; infer_instance

def q (k : Fin 3) (v : Core) : Core :=
  (if k=0 then [4, 8, 5, 9, 0, 2, 7, 6, 1, 3, 11, 10, 13, 12, 15, 14, 17, 16] else if k=1 then [1, 0, 3, 2, 7, 6, 5, 4, 11, 10, 9, 8, 13, 12, 15, 14, 17, 16] else [1, 0, 5, 9, 7, 2, 13, 4, 11, 3, 16, 8, 17, 6, 15, 14, 10, 12] : List Core)[v.val]!

theorem q_inv (k : Fin 3) : Function.Involutive (q k) := by
  change ∀ v : Core,q k (q k v)=v
  fin_cases k <;> decide

theorem q_adj : ∀ k (v : Core),core.Adj v (q k v) := by decide

def markedCost (m : Core→Core) : Nat :=
  (univ.filter (fun i : Port => m (a i)=b i)).card

private def bit (P : Prop) [Decidable P] : Nat := if P then 1 else 0

/-- Number of the four old boundary edges that remain in the matching
and are thus still absent from its complementary rank. -/
def cutCount (m : Core→Core) : Nat :=
  bit (m 0=4) + bit (m 1=8) + bit (m 2=5) + bit (m 3=9)

theorem witness_counts :
    markedCost (q 0)=0 ∧ cutCount (q 0)=4 ∧
    markedCost (q 1)=0 ∧ cutCount (q 1)=0 ∧
    markedCost (q 2)=2 ∧ cutCount (q 2)=2 := by decide

theorem two_release_cost (m : Core→Core) (inv : Function.Involutive m)
    (adj : ∀ v,core.Adj v (m v)) (count : cutCount m=2) :
    2 ≤ markedCost m := by
  have rev {u v : Core} (e : m u=v) : m v=u := by rw [←e,inv]
  have no {u v w : Core} (h : m v=w) (ne : u≠w) : m u≠v :=
    fun e=>ne ((rev e).symm.trans h)
  have opts0 : m 0=1 ∨ m 0=3 ∨ m 0=4 := by
    have h : ∀ w : Core,core.Adj 0 w → w=1 ∨ w=3 ∨ w=4 := by decide
    exact h _ (adj 0)
  have opts1 : m 1=0 ∨ m 1=2 ∨ m 1=8 := by
    have h : ∀ w : Core,core.Adj 1 w → w=0 ∨ w=2 ∨ w=8 := by decide
    exact h _ (adj 1)
  have opts2 : m 2=1 ∨ m 2=3 ∨ m 2=5 := by
    have h : ∀ w : Core,core.Adj 2 w → w=1 ∨ w=3 ∨ w=5 := by decide
    exact h _ (adj 2)
  have opts3 : m 3=0 ∨ m 3=2 ∨ m 3=9 := by
    have h : ∀ w : Core,core.Adj 3 w → w=0 ∨ w=2 ∨ w=9 := by decide
    exact h _ (adj 3)
  have opts4 : m 4=0 ∨ m 4=5 ∨ m 4=7 := by
    have h : ∀ w : Core,core.Adj 4 w → w=0 ∨ w=5 ∨ w=7 := by decide
    exact h _ (adj 4)
  have opts5 : m 5=2 ∨ m 5=4 ∨ m 5=6 := by
    have h : ∀ w : Core,core.Adj 5 w → w=2 ∨ w=4 ∨ w=6 := by decide
    exact h _ (adj 5)
  have opts6 : m 6=5 ∨ m 6=7 ∨ m 6=13 := by
    have h : ∀ w : Core,core.Adj 6 w → w=5 ∨ w=7 ∨ w=13 := by decide
    exact h _ (adj 6)
  have opts7 : m 7=4 ∨ m 7=6 ∨ m 7=14 := by
    have h : ∀ w : Core,core.Adj 7 w → w=4 ∨ w=6 ∨ w=14 := by decide
    exact h _ (adj 7)
  have opts8 : m 8=1 ∨ m 8=9 ∨ m 8=11 := by
    have h : ∀ w : Core,core.Adj 8 w → w=1 ∨ w=9 ∨ w=11 := by decide
    exact h _ (adj 8)
  have opts9 : m 9=3 ∨ m 9=8 ∨ m 9=10 := by
    have h : ∀ w : Core,core.Adj 9 w → w=3 ∨ w=8 ∨ w=10 := by decide
    exact h _ (adj 9)
  have opts10 : m 10=9 ∨ m 10=11 ∨ m 10=16 := by
    have h : ∀ w : Core,core.Adj 10 w → w=9 ∨ w=11 ∨ w=16 := by decide
    exact h _ (adj 10)
  have opts11 : m 11=8 ∨ m 11=10 ∨ m 11=17 := by
    have h : ∀ w : Core,core.Adj 11 w → w=8 ∨ w=10 ∨ w=17 := by decide
    exact h _ (adj 11)

  have notA : ¬(m 0=4 ∧ m 2=5) := by
    rintro ⟨h0,h2⟩
    have notB1 : m 1≠8 := by
      intro h1
      simp [cutCount,bit,h0,h1,h2] at count
      omega
    rcases opts1 with e|e|e
    · exact no h0 (by decide) e
    · exact no h2 (by decide) e
    · exact notB1 e
  have notB : ¬(m 1=8 ∧ m 3=9) := by
    rintro ⟨h1,h3⟩
    have notA0 : m 0≠4 := by
      intro h0
      simp [cutCount,bit,h0,h1,h3] at count
      omega
    rcases opts0 with e|e|e
    · exact no h1 (by decide) e
    · exact no h3 (by decide) e
    · exact notA0 e
  have atA : (m 0=4 ∧ m 2≠5) ∨ (m 0≠4 ∧ m 2=5) := by
    by_cases h0 : m 0=4 <;> by_cases h1 : m 1=8 <;>
      by_cases h2 : m 2=5 <;> by_cases h3 : m 3=9 <;>
      simp_all [cutCount,bit]
  have atB : (m 1=8 ∧ m 3≠9) ∨ (m 1≠8 ∧ m 3=9) := by
    by_cases h0 : m 0=4 <;> by_cases h1 : m 1=8 <;>
      by_cases h2 : m 2=5 <;> by_cases h3 : m 3=9 <;>
      simp_all [cutCount,bit]
  have hitA : m 6=13 ∨ m 7=14 := by
    rcases atA with ⟨h0,h2⟩|⟨h0,h2⟩
    · have h4 := rev h0
      have h5 : m 5=6 := by
        rcases opts5 with e|e|e
        · exact (h2 (rev e)).elim
        · exact (no h4 (by decide) e).elim
        · exact e
      have h6 := rev h5
      right
      rcases opts7 with e|e|e
      · exact (no h4 (by decide) e).elim
      · exact (no h6 (by decide) e).elim
      · exact e
    · have h5 := rev h2
      have h4 : m 4=7 := by
        rcases opts4 with e|e|e
        · exact (h0 (rev e)).elim
        · exact (no h5 (by decide) e).elim
        · exact e
      have h7 := rev h4
      left
      rcases opts6 with e|e|e
      · exact (no h5 (by decide) e).elim
      · exact (no h7 (by decide) e).elim
      · exact e
  have hitB : m 10=16 ∨ m 11=17 := by
    rcases atB with ⟨h1,h3⟩|⟨h1,h3⟩
    · have h8 := rev h1
      have h9 : m 9=10 := by
        rcases opts9 with e|e|e
        · exact (h3 (rev e)).elim
        · exact (no h8 (by decide) e).elim
        · exact e
      have h10 := rev h9
      right
      rcases opts11 with e|e|e
      · exact (no h8 (by decide) e).elim
      · exact (no h10 (by decide) e).elim
      · exact e
    · have h9 := rev h3
      have h8 : m 8=11 := by
        rcases opts8 with e|e|e
        · exact (h1 (rev e)).elim
        · exact (no h9 (by decide) e).elim
        · exact e
      have h11 := rev h8
      left
      rcases opts10 with e|e|e
      · exact (no h9 (by decide) e).elim
      · exact (no h11 (by decide) e).elim
      · exact e
  have two {i j : Port} (hi : m (a i)=b i) (hj : m (a j)=b j) (ne : i≠j) :
      2 ≤ markedCost m := by
    have subset : ({i,j}:Finset Port) ⊆ univ.filter (fun k => m (a k)=b k) := by
      intro k hk
      rcases (show k=i∨k=j by simpa using hk) with rfl|rfl <;> simp [hi,hj]
    simpa [ne,markedCost] using card_le_card subset
  rcases hitA with p|p <;> rcases hitB with q|q
  · exact two (i:=.inl (.inl false)) (j:=.inl (.inr false)) p q (by decide)
  · exact two (i:=.inl (.inl false)) (j:=.inl (.inr true)) p q (by decide)
  · exact two (i:=.inl (.inl true)) (j:=.inl (.inr false)) p q (by decide)
  · exact two (i:=.inl (.inl true)) (j:=.inl (.inr true)) p q (by decide)

theorem no_cheap_two_release (m : Core→Core) (inv : Function.Involutive m)
    (adj : ∀ v,core.Adj v (m v)) (budget : markedCost m≤1) : cutCount m≠2 := by
  intro h
  have z := two_release_cost m inv adj h
  omega

def slot (i : Fin 6) : Port :=
  if i=0 then .inl (.inl false) else if i=1 then .inl (.inl true) else
  if i=2 then .inl (.inr false) else if i=3 then .inl (.inr true) else
  if i=4 then .inr false else .inr true

def decode (n : Nat) : Board := if n<18 then .inl (Fin.ofNat' 18 n) else .inr (slot (Fin.ofNat' 6 (n-18)))
def route (l : List Nat) : List Board := l.map decode


def square : Finset Core := {0,1,2,3}
set_option maxRecDepth 8000 in
theorem exact_boundary :
    boundary core (fun x => decide (x∈square)) =
      ({(0,4),(1,8),(2,5),(3,9)} : Finset (Core×Core)) := by
  ext e
  have tab : ∀ e : Core×Core,(e.1∈square ∧ e.2∉square ∧ core.Adj e.1 e.2) ↔
      e∈({(0,4),(1,8),(2,5),(3,9)} : Finset (Core×Core)) := by decide
  simpa [boundary] using tab e

set_option maxRecDepth 8000 in
theorem induced_square : ∀ u v : Core,u∈square → v∈square →
    let L : List (Core×Core) := [(0,1),(1,2),(2,3),(3,0)]
    (core.Adj u v ↔ (u,v)∈L ∨ (v,u)∈L) := by decide

set_option maxRecDepth 8000 in
theorem exact_twelve_exchange :
    ∀ x y : Core, ((q 0 x=y ∧ q 1 x≠y) ∨ (q 1 x=y ∧ q 0 x≠y)) ↔
      let L : List (Core×Core) := [(0,4),(4,7),(7,6),(6,5),(5,2),(2,3),
        (3,9),(9,10),(10,11),(11,8),(8,1),(1,0)]
      (x,y)∈L ∨ (y,x)∈L := by decide

theorem diagonal_links :
    core.Adj 0 4 ∧ core.Adj 4 7 ∧ core.Adj 7 6 ∧ core.Adj 6 5 ∧ core.Adj 5 2 ∧
    core.Adj 1 8 ∧ core.Adj 8 11 ∧ core.Adj 11 10 ∧ core.Adj 10 9 ∧ core.Adj 9 3 := by decide

private def triple (a b c : Nat) : Finset Board := {decode a,decode b,decode c}
private def tiles : Finset (Finset Board) :=
  {triple 18 6 5,triple 0 4 22,triple 14 19 7,triple 17 12 13,
   triple 20 16 15,triple 8 11 21,triple 1 2 3,triple 10 9 23}

theorem unrestricted_factor : HasFactor board := by
  refine ⟨tiles,?_,?_,?_⟩
  · change ∀ A ∈ tiles,A.card=3 ∧ ∃ c∈A,∀ x∈A,x≠c → board.Adj c x
    decide
  · decide
  · decide
open RemoteT2CompletionTransfer (eraseEdge)
abbrev Host := RemoteSpacedPrismHandle.Host marks
abbrev HostV := RemoteSpacedPrismHandle.V4 Core
theorem host_cube : ∀ v, Host.degree v=3 :=
  RemoteSpacedPrismHandle.cubic marks core_cube
theorem host_small : SmallTrivial Host :=
  RemoteSpacedPrismHandle.small_trivial marks core_cube core_cyclic_four
theorem host_three_connected : ThreeConnected Host :=
  SquareCap.three_connected_of_small_trivial _ host_cube (by decide) host_small
theorem exact_order : Fintype.card HostV=26 ∧ Fintype.card Board=24 := by decide
theorem exact_remote :
    Host.Adj (pole false) (pole true) ∧ Host.Adj (endThird false) (endThird true) ∧
    RemoteT2Scope.Remote Host (pole false) (endThird false) (endThird true) :=
  ⟨RemoteSpacedPrismHandle.pole_join marks,RemoteSpacedPrismHandle.remote_edge marks,
    RemoteSpacedPrismHandle.remote marks⟩

theorem exact_board :
    Function.Injective (embed (V:=Core)) ∧
    (∀ x : HostV,x≠pole false∧x≠pole true ↔ ∃ y : Board,embed y=x) ∧
    (∀ a b : Board,board.Adj a b ↔
      (eraseEdge Host (endThird false) (endThird true)).Adj (embed a) (embed b)) :=
  ⟨RemoteSpacedPrismHandle.embed_injective,RemoteSpacedPrismHandle.embed_range,
    RemoteSpacedPrismHandle.exact_survivor marks⟩

theorem wide (c : Board→Bool) (h : ∀ b,NontrivialSide c b) :
    3≤(boundary board c).card :=
  RemoteSpacedPrismWidth.expanded_wide marks core_cube core_cyclic_four c h







#print axioms witness_counts
#print axioms two_release_cost
#print axioms no_cheap_two_release
#print axioms exact_boundary
#print axioms exact_twelve_exchange
#print axioms unrestricted_factor
#print axioms host_three_connected
#print axioms exact_board
#print axioms wide
end KelmansCactus.AtomicBridge.DiagonalReleaseFixture
