import RemoteSpacedPrismLayout
import RemoteCutCertificate
import RemoteSpacedPrismWidth
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Chain

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.MinOneEight
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide ThreeConnected boundary HasFactor FactorOn IsTile)

abbrev Core := Fin 18

def succ (v : Core) : Core := ⟨(v.val+1)%18,Nat.mod_lt _ (by decide)⟩

def mate (v : Core) : Core :=
  ([12, 4, 16, 8, 1, 14, 9, 11, 3, 6, 15, 7, 0, 17, 5, 10, 2, 13] : List Core)[v.val]!

private theorem mate_symm : ∀ v, mate (mate v)=v := by decide
private theorem mate_ne : ∀ v, mate v≠v := by decide
private theorem succ_ne : ∀ v, succ v≠v := by decide

def Adj (v w : Core) : Prop := succ v=w ∨ succ w=v ∨ mate v=w
instance (v w : Core) : Decidable (Adj v w) := by unfold Adj; infer_instance

abbrev core : SimpleGraph Core where
  Adj := Adj
  symm := by
    intro v w h
    rcases h with h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [←h,mate_symm]))
  loopless v h := h.elim (succ_ne v) (fun h=>h.elim (succ_ne v) (mate_ne v))

instance : DecidableRel core.Adj := fun v w => inferInstanceAs (Decidable (Adj v w))

theorem core_cube : ∀ v, core.degree v=3 := by decide

def a : Port → Core
  | .inl (.inl false) => 7
  | .inl (.inl true) => 1
  | .inl (.inr false) => 3
  | .inl (.inr true) => 9
  | .inr false => 5
  | .inr true => 16

def b : Port → Core
  | .inl (.inl false) => 8
  | .inl (.inl true) => 2
  | .inl (.inr false) => 4
  | .inl (.inr true) => 10
  | .inr false => 14
  | .inr true => 17

def marks : Marks core Port where
  a := a
  b := b
  edge := by decide
  separated := by
    intro i j x
    have h : ∀ i j : Port, ∀ x : Core, x=a i∨x=b i → x=a j∨x=b j → i=j := by decide
    exact h i j x

abbrev board := marks.expanded


private def edgeTable : RemoteCutCertificate.Table 18 where
  edges := [(0, 1), (0, 12), (0, 17), (1, 2), (1, 4), (2, 3), (2, 16), (3, 4), (3, 8), (4, 5), (5, 6), (5, 14), (6, 7), (6, 9), (7, 8), (7, 11), (8, 9), (9, 10), (10, 11), (10, 15), (11, 12), (12, 13), (13, 14), (13, 17), (14, 15), (15, 16), (16, 17)]
  sorted := by decide
  nodup := by decide

private theorem table_eq : edgeTable.graph = core := by
  ext x y
  have all : ∀ x y : Core, edgeTable.graph.Adj x y ↔ core.Adj x y := by decide
  exact all x y

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem table_valid :
    edgeTable.cert 4 1 [12,0,17,1,2,16,3,4,5,14,15,6,7,8,9,10,11]
      (RemoteCutCertificate.Table.base 13)=true := by decide

theorem core_cyclic_four : SmallTrivial core := by
  rw [←table_eq]
  exact edgeTable.cyclic_four table_valid


abbrev Board := Core ⊕ Port

instance : DecidableRel board.Adj := by
  intro x y
  rcases x with (x|i) <;> rcases y with (y|j)
  · change Decidable (core.Adj x y ∧ ¬∃ i : Port, (x=a i ∧ y=b i) ∨ (x=b i ∧ y=a i))
    infer_instance
  · change Decidable (x=a j ∨ x=b j); infer_instance
  · change Decidable (y=a i ∨ y=b i); infer_instance
  · change Decidable False; infer_instance

def q (t : Bool) (v : Core) : Core :=
  (if t then [12, 4, 16, 8, 1, 6, 5, 11, 3, 10, 9, 7, 0, 17, 15, 14, 2, 13] else [1, 0, 16, 8, 5, 4, 7, 6, 3, 10, 9, 12, 11, 17, 15, 14, 2, 13] : List Core)[v.val]!
theorem q_inv (t : Bool) : Function.Involutive (q t) := by
  change ∀ v : Core,q t (q t v)=v
  cases t <;> decide

theorem q_adj : ∀ t (v : Core),core.Adj v (q t v) := by decide


def omitted : Port := .inl (.inr true)
theorem q_omission : ∀ t (i : Port),(q t (a i)=b i) ↔ i=omitted := by decide

def markedCost (m : Core→Core) : Nat :=
  (univ.filter (fun i : Port => m (a i)=b i)).card

theorem q_cost : ∀ t : Bool,markedCost (q t)=1 := by decide

theorem no_zero_matching (m : Core→Core) (inv : Function.Involutive m)
    (adj : ∀ v,core.Adj v (m v)) (avoid : ∀ i : Port, m (a i)≠b i) : False := by
  have rev {u v : Core} (e : m u=v) : m v=u := by rw [←e,inv]
  have no {u v w : Core} (h : m v=w) (ne : u≠w) : m u≠v :=
    fun e=>ne ((rev e).symm.trans h)
  have opts1 : m 1=0 ∨ m 1=2 ∨ m 1=4 := by
    have h : ∀ w : Core,core.Adj 1 w → w=0 ∨ w=2 ∨ w=4 := by decide
    exact h _ (adj 1)
  have opts3 : m 3=2 ∨ m 3=4 ∨ m 3=8 := by
    have h : ∀ w : Core,core.Adj 3 w → w=2 ∨ w=4 ∨ w=8 := by decide
    exact h _ (adj 3)
  have opts4 : m 4=1 ∨ m 4=3 ∨ m 4=5 := by
    have h : ∀ w : Core,core.Adj 4 w → w=1 ∨ w=3 ∨ w=5 := by decide
    exact h _ (adj 4)
  have opts5 : m 5=4 ∨ m 5=6 ∨ m 5=14 := by
    have h : ∀ w : Core,core.Adj 5 w → w=4 ∨ w=6 ∨ w=14 := by decide
    exact h _ (adj 5)
  have opts7 : m 7=6 ∨ m 7=8 ∨ m 7=11 := by
    have h : ∀ w : Core,core.Adj 7 w → w=6 ∨ w=8 ∨ w=11 := by decide
    exact h _ (adj 7)
  have opts9 : m 9=6 ∨ m 9=8 ∨ m 9=10 := by
    have h : ∀ w : Core,core.Adj 9 w → w=6 ∨ w=8 ∨ w=10 := by decide
    exact h _ (adj 9)
  have opts10 : m 10=9 ∨ m 10=11 ∨ m 10=15 := by
    have h : ∀ w : Core,core.Adj 10 w → w=9 ∨ w=11 ∨ w=15 := by decide
    exact h _ (adj 10)
  have opts12 : m 12=0 ∨ m 12=11 ∨ m 12=13 := by
    have h : ∀ w : Core,core.Adj 12 w → w=0 ∨ w=11 ∨ w=13 := by decide
    exact h _ (adj 12)
  have opts14 : m 14=5 ∨ m 14=13 ∨ m 14=15 := by
    have h : ∀ w : Core,core.Adj 14 w → w=5 ∨ w=13 ∨ w=15 := by decide
    exact h _ (adj 14)
  have opts16 : m 16=2 ∨ m 16=15 ∨ m 16=17 := by
    have h : ∀ w : Core,core.Adj 16 w → w=2 ∨ w=15 ∨ w=17 := by decide
    exact h _ (adj 16)
  have opts17 : m 17=0 ∨ m 17=13 ∨ m 17=16 := by
    have h : ∀ w : Core,core.Adj 17 w → w=0 ∨ w=13 ∨ w=16 := by decide
    exact h _ (adj 17)
  have variants : m 1=0 ∨ m 1=4 := by
    rcases opts1 with e|e|e
    · exact Or.inl e
    · exact (avoid (.inl (.inl true)) e).elim
    · exact Or.inr e
  rcases variants with h1|h1
  · have h0 := rev h1
    have h4 : m 4=5 := by
      rcases opts4 with e|e|e
      · exact (no h1 (by decide) e).elim
      · exact (avoid (.inl (.inr false)) (rev e)).elim
      · exact e
    have h5 := rev h4
    have h17 : m 17=13 := by
      rcases opts17 with e|e|e
      · exact (no h0 (by decide) e).elim
      · exact e
      · exact (avoid (.inr true) (rev e)).elim
    have h13 := rev h17
    have h12 : m 12=11 := by
      rcases opts12 with e|e|e
      · exact (no h0 (by decide) e).elim
      · exact e
      · exact (no h13 (by decide) e).elim
    have h11 := rev h12
    have h7 : m 7=6 := by
      rcases opts7 with e|e|e
      · exact e
      · exact (avoid (.inl (.inl false)) e).elim
      · exact (no h11 (by decide) e).elim
    have h6 := rev h7
    have h9 : m 9=8 := by
      rcases opts9 with e|e|e
      · exact (no h6 (by decide) e).elim
      · exact e
      · exact (avoid (.inl (.inr true)) e).elim
    have h8 := rev h9
    have h3 : m 3=2 := by
      rcases opts3 with e|e|e
      · exact e
      · exact (no h4 (by decide) e).elim
      · exact (no h8 (by decide) e).elim
    have h2 := rev h3
    have h10 : m 10=15 := by
      rcases opts10 with e|e|e
      · exact (no h9 (by decide) e).elim
      · exact (no h11 (by decide) e).elim
      · exact e
    have h15 := rev h10
    have h14 : False := by
      rcases opts14 with e|e|e
      · exact (no h5 (by decide) e).elim
      · exact (no h13 (by decide) e).elim
      · exact (no h15 (by decide) e).elim
    exact h14
  · have h4 := rev h1
    have h5 : m 5=6 := by
      rcases opts5 with e|e|e
      · exact (no h4 (by decide) e).elim
      · exact e
      · exact (avoid (.inr false) e).elim
    have h6 := rev h5
    have h7 : m 7=11 := by
      rcases opts7 with e|e|e
      · exact (no h6 (by decide) e).elim
      · exact (avoid (.inl (.inl false)) e).elim
      · exact e
    have h11 := rev h7
    have h9 : m 9=8 := by
      rcases opts9 with e|e|e
      · exact (no h6 (by decide) e).elim
      · exact e
      · exact (avoid (.inl (.inr true)) e).elim
    have h8 := rev h9
    have h3 : m 3=2 := by
      rcases opts3 with e|e|e
      · exact e
      · exact (no h4 (by decide) e).elim
      · exact (no h8 (by decide) e).elim
    have h2 := rev h3
    have h10 : m 10=15 := by
      rcases opts10 with e|e|e
      · exact (no h9 (by decide) e).elim
      · exact (no h11 (by decide) e).elim
      · exact e
    have h15 := rev h10
    have h16 : False := by
      rcases opts16 with e|e|e
      · exact (no h2 (by decide) e).elim
      · exact (no h15 (by decide) e).elim
      · exact (avoid (.inr true) e).elim
    exact h16


theorem cost_lower_bound (m : Core→Core) (inv : Function.Involutive m)
    (adj : ∀ v,core.Adj v (m v)) : 1 ≤ markedCost m := by
  by_contra! h
  have hc : markedCost m=0 := by omega
  apply no_zero_matching m inv adj
  intro i eq
  have mem : i ∈ (univ.filter (fun i : Port=>m (a i)=b i)) :=
    mem_filter.mpr ⟨mem_univ _,eq⟩
  have z := card_pos.mpr ⟨i,mem⟩
  exact (not_lt_of_ge (le_of_eq hc)) z

theorem min_one : (∃ m : Core→Core, Function.Involutive m ∧
      (∀ v,core.Adj v (m v)) ∧ markedCost m=1) ∧
    (∀ m : Core→Core, Function.Involutive m → (∀ v,core.Adj v (m v)) → 1 ≤ markedCost m) :=
  ⟨⟨q false,q_inv false,q_adj false,q_cost false⟩,cost_lower_bound⟩

/-- The complementary degree-two subgraph of the involutive matching. -/
def rankOf (m : Core→Core) (inv : Function.Involutive m) : SimpleGraph Core where
  Adj x y := core.Adj x y ∧ m x ≠ y
  symm := fun x y h=>⟨h.1.symm,fun e=>h.2 (by rw [←e,inv])⟩
  loopless := fun x h=>core.loopless x h.1

instance (m : Core→Core) (inv : Function.Involutive m) : DecidableRel (rankOf m inv).Adj :=
  fun x y=>inferInstanceAs (Decidable (core.Adj x y ∧ m x ≠ y))

/-- Available edges in the rebuilt graph are those of the 2-factor,
subdivided wherever marked, together with the subdivided omitted marks. -/
def rebuilt (F : SimpleGraph Core) : SimpleGraph Board where
  Adj x y := board.Adj x y ∧ match x,y with
    | .inl u,.inl v => F.Adj u v
    | _,_ => True
  symm := by
    rintro (x|i) (y|j) h
    · exact ⟨h.1.symm,h.2.symm⟩
    all_goals exact ⟨h.1.symm,trivial⟩
  loopless x h := board.loopless x h.1

instance (F : SimpleGraph Core) [DecidableRel F.Adj] : DecidableRel (rebuilt F).Adj := by
  rintro (x|i) (y|j)
  all_goals change Decidable (_ ∧ _)
  all_goals infer_instance

def Closed (G : SimpleGraph Board) (s : Finset Board) : Prop :=
  ∀ x y : Board,x∈s → G.Adj x y → y∈s
instance (G : SimpleGraph Board) [DecidableRel G.Adj] (s : Finset Board) : Decidable (Closed G s) := by
  unfold Closed
  infer_instance


def slot (i : Fin 6) : Port :=
  if i=0 then .inl (.inl false) else if i=1 then .inl (.inl true) else
  if i=2 then .inl (.inr false) else if i=3 then .inl (.inr true) else
  if i=4 then .inr false else .inr true

def decode (n : Nat) : Board := if n<18 then .inl (Fin.ofNat' 18 n) else .inr (slot (Fin.ofNat' 6 (n-18)))
def route (l : List Nat) : List Board := l.map decode

abbrev ranked (t : Bool) := rankOf (q t) (q_inv t)
theorem ranked_degree : ∀ t,∀ x,(ranked t).degree x=2 := by decide


def oldShore : Finset Core := {1,2,3,4}
set_option maxRecDepth 8000 in
theorem square_boundary :
    boundary core (fun x => decide (x∈oldShore)) =
      ({(1,0),(2,16),(3,8),(4,5)} : Finset (Core×Core)) := by
  ext e
  have tab : ∀ e : Core×Core,(e.1∈oldShore ∧ e.2∉oldShore ∧ core.Adj e.1 e.2) ↔
      e∈({(1,0),(2,16),(3,8),(4,5)} : Finset (Core×Core)) := by decide
  simpa [boundary] using tab e

theorem old_cut_all_omitted :
    q false 1=0 ∧ q false 2=16 ∧ q false 3=8 ∧ q false 4=5 := by decide

theorem new_cut_exact :
    (ranked true).Adj 1 0 ∧ ¬(ranked true).Adj 2 16 ∧
    ¬(ranked true).Adj 3 8 ∧ (ranked true).Adj 4 5 := by decide

set_option maxRecDepth 8000 in
theorem induced_square : ∀ u v : Core,u∈oldShore → v∈oldShore →
    let L : List (Core×Core) := [(1,2),(2,3),(3,4),(4,1)]
    (core.Adj u v ↔ (u,v)∈L ∨ (v,u)∈L) := by decide

theorem exact_eight_exchange :
    ∀ x y : Core, ((q false x=y ∧ q true x≠y) ∨ (q true x=y ∧ q false x≠y)) ↔
      let L : List (Core×Core) := [(0,1),(1,4),(4,5),(5,6),(6,7),(7,11),(11,12),(12,0)]
      (x,y)∈L ∨ (y,x)∈L := by decide

theorem eight_alternates :
    q false 0=1 ∧ q true 1=4 ∧ q false 4=5 ∧ q true 5=6 ∧
    q false 6=7 ∧ q true 7=11 ∧ q false 11=12 ∧ q true 12=0 := by decide

def smallRoute : List Board := route [1,4,20,3,2,19]
def largeRoute : List Board := route [6,5,22,14,13,12,0,17,23,16,15,10,11,7,18,8,9,21]

set_option maxRecDepth 8000 in
theorem initial_geometry :
    smallRoute.Nodup ∧ largeRoute.Nodup ∧ smallRoute.length=6 ∧ largeRoute.length=18 ∧
    Closed (rebuilt (ranked false)) smallRoute.toFinset ∧
    Closed (rebuilt (ranked false)) largeRoute.toFinset ∧
    Disjoint smallRoute.toFinset largeRoute.toFinset ∧
    smallRoute.toFinset ∪ largeRoute.toFinset = univ ∧
    smallRoute.Chain' (rebuilt (ranked false)).Adj ∧
    largeRoute.Chain' (rebuilt (ranked false)).Adj := by decide

def finalRoute : List Board := route [6,7,18,8,9,21,10,11,12,13,14,22,5,4,20,3,2,19,1,0,17,23,16,15]

theorem final_geometry :
    finalRoute.Nodup ∧ finalRoute.length=24 ∧ finalRoute.toFinset=univ ∧
    finalRoute.Chain' (rebuilt (ranked true)).Adj := by decide

private theorem reach_of_route {G : SimpleGraph Board} {a b : Board} (L : List Board)
    (p : (a::L).Chain' G.Adj) (hm : b∈a::L) : G.Reachable a b := by
  induction L generalizing a with
  | nil =>
    have h : b=a := by simpa using hm
    subst b
    exact Reachable.refl _
  | cons c L ih =>
    rcases List.mem_cons.mp hm with e|e
    · subst b
      exact Reachable.refl _
    · have eq := List.chain'_cons.mp p
      exact eq.1.reachable.trans (ih eq.2 e)

theorem final_connected : (rebuilt (ranked true)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (rebuilt (ranked true))).mpr
  refine ⟨decode 6,?_⟩
  intro x
  apply reach_of_route (route [7,18,8,9,21,10,11,12,13,14,22,5,4,20,3,2,19,1,0,17,23,16,15])
  · exact final_geometry.2.2.2
  · have hx : x∈finalRoute.toFinset := by rw [final_geometry.2.2.1]; exact mem_univ _
    exact List.mem_toFinset.mp hx

private def triple (a b c : Nat) : Finset Board := {decode a,decode b,decode c}
private def tiles : Finset (Finset Board) :=
  {triple 6 7 18,triple 8 9 21,triple 10 11 12,triple 13 14 22,
   triple 5 4 20,triple 3 2 19,triple 1 0 17,triple 23 16 15}

theorem final_factor : HasFactor (rebuilt (ranked true)) := by
  refine ⟨tiles,?_,?_,?_⟩
  · change ∀ A ∈ tiles,A.card=3 ∧ ∃ c∈A,∀ x∈A,x≠c → (rebuilt (ranked true)).Adj c x
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






#print axioms min_one
#print axioms square_boundary
#print axioms exact_eight_exchange
#print axioms initial_geometry
#print axioms final_connected
#print axioms final_factor
#print axioms host_three_connected
#print axioms exact_board
#print axioms wide
end KelmansCactus.AtomicBridge.MinOneEight
