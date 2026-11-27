import RemoteSpacedPrismLayout
import RemoteCutCertificate
import RemoteSpacedPrismWidth
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Chain

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.SquareUnionLock
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide ThreeConnected boundary HasFactor FactorOn IsTile)

abbrev Core := Fin 18

def succ (v : Core) : Core := ⟨(v.val+1)%18,Nat.mod_lt _ (by decide)⟩

def mate (v : Core) : Core :=
  ([11, 6, 5, 12, 15, 2, 1, 10, 16, 14, 7, 0, 3, 17, 9, 4, 8, 13] : List Core)[v.val]!

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
  | .inl (.inl false) => 9
  | .inl (.inl true) => 14
  | .inl (.inr false) => 2
  | .inl (.inr true) => 1
  | .inr false => 0
  | .inr true => 12

def b : Port → Core
  | .inl (.inl false) => 10
  | .inl (.inl true) => 15
  | .inl (.inr false) => 5
  | .inl (.inr true) => 6
  | .inr false => 11
  | .inr true => 13

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
  edges := [(0, 1), (0, 11), (0, 17), (1, 2), (1, 6), (2, 3), (2, 5), (3, 4), (3, 12), (4, 5), (4, 15), (5, 6), (6, 7), (7, 8), (7, 10), (8, 9), (8, 16), (9, 10), (9, 14), (10, 11), (11, 12), (12, 13), (13, 14), (13, 17), (14, 15), (15, 16), (16, 17)]
  sorted := by decide
  nodup := by decide

private theorem table_eq : edgeTable.graph = core := by
  ext x y
  have all : ∀ x y : Core, edgeTable.graph.Adj x y ↔ core.Adj x y := by decide
  exact all x y

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem table_valid :
    edgeTable.cert 4 1 [0,1,2,3,12,4,5,6,7,10,8,9,13,14,15,16,17]
      (RemoteCutCertificate.Table.base 11)=true := by decide

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
  (if t then [11, 2, 1, 12, 15, 6, 5, 10, 16, 14, 7, 0, 3, 17, 9, 4, 8, 13] else [11, 2, 1, 12, 15, 6, 5, 10, 9, 8, 7, 0, 3, 14, 13, 4, 17, 16] : List Core)[v.val]!
theorem q_inv (t : Bool) : Function.Involutive (q t) := by
  change ∀ v : Core,q t (q t v)=v
  cases t <;> decide

theorem q_adj : ∀ t (v : Core),core.Adj v (q t v) := by decide

def omitted : Port := .inr false
theorem q_omission : ∀ t (i : Port),(q t (a i)=b i) ↔ i=omitted := by decide

def Prescribed (m : Core→Core) : Prop :=
  Function.Involutive m ∧
  (∀ v,core.Adj v (m v)) ∧ m 0=11 ∧
  (∀ i : Port,i≠omitted → m (a i)≠b i)

theorem classifies (m : Core→Core) (P : Prescribed m) :
    ∃ t : Bool,m = q t := by
  obtain ⟨inv,adj,h0,avoid⟩ := P
  have rev {u v : Core} (e : m u=v) : m v=u := by rw [←e,inv]
  have no {u v w : Core} (h : m v=w) (ne : u≠w) : m u≠v :=
    fun e=>ne ((rev e).symm.trans h)
  have h11 := rev h0
  have opts1 : m 1=0 ∨ m 1=2 ∨ m 1=6 := by
    have h : ∀ w : Core,core.Adj 1 w → w=0 ∨ w=2 ∨ w=6 := by decide
    exact h _ (adj 1)
  have opts4 : m 4=3 ∨ m 4=5 ∨ m 4=15 := by
    have h : ∀ w : Core,core.Adj 4 w → w=3 ∨ w=5 ∨ w=15 := by decide
    exact h _ (adj 4)
  have opts6 : m 6=1 ∨ m 6=5 ∨ m 6=7 := by
    have h : ∀ w : Core,core.Adj 6 w → w=1 ∨ w=5 ∨ w=7 := by decide
    exact h _ (adj 6)
  have opts8 : m 8=7 ∨ m 8=9 ∨ m 8=16 := by
    have h : ∀ w : Core,core.Adj 8 w → w=7 ∨ w=9 ∨ w=16 := by decide
    exact h _ (adj 8)
  have opts9 : m 9=8 ∨ m 9=10 ∨ m 9=14 := by
    have h : ∀ w : Core,core.Adj 9 w → w=8 ∨ w=10 ∨ w=14 := by decide
    exact h _ (adj 9)
  have opts10 : m 10=7 ∨ m 10=9 ∨ m 10=11 := by
    have h : ∀ w : Core,core.Adj 10 w → w=7 ∨ w=9 ∨ w=11 := by decide
    exact h _ (adj 10)
  have opts12 : m 12=3 ∨ m 12=11 ∨ m 12=13 := by
    have h : ∀ w : Core,core.Adj 12 w → w=3 ∨ w=11 ∨ w=13 := by decide
    exact h _ (adj 12)
  have opts13 : m 13=12 ∨ m 13=14 ∨ m 13=17 := by
    have h : ∀ w : Core,core.Adj 13 w → w=12 ∨ w=14 ∨ w=17 := by decide
    exact h _ (adj 13)
  have opts16 : m 16=8 ∨ m 16=15 ∨ m 16=17 := by
    have h : ∀ w : Core,core.Adj 16 w → w=8 ∨ w=15 ∨ w=17 := by decide
    exact h _ (adj 16)
  have opts17 : m 17=0 ∨ m 17=13 ∨ m 17=16 := by
    have h : ∀ w : Core,core.Adj 17 w → w=0 ∨ w=13 ∨ w=16 := by decide
    exact h _ (adj 17)
  have h1 : m 1=2 := by
    rcases opts1 with e|e|e
    · exact (no h0 (by decide) e).elim
    · exact e
    · exact (avoid (.inl (.inr true)) (by decide) e).elim
  have h2 := rev h1
  have h10 : m 10=7 := by
    rcases opts10 with e|e|e
    · exact e
    · exact (avoid (.inl (.inl false)) (by decide) (rev e)).elim
    · exact (no h11 (by decide) e).elim
  have h7 := rev h10
  have h6 : m 6=5 := by
    rcases opts6 with e|e|e
    · exact (no h1 (by decide) e).elim
    · exact e
    · exact (no h7 (by decide) e).elim
  have h5 := rev h6
  have h12 : m 12=3 := by
    rcases opts12 with e|e|e
    · exact e
    · exact (no h11 (by decide) e).elim
    · exact (avoid (.inr true) (by decide) e).elim
  have h3 := rev h12
  have h4 : m 4=15 := by
    rcases opts4 with e|e|e
    · exact (no h3 (by decide) e).elim
    · exact (no h5 (by decide) e).elim
    · exact e
  have h15 := rev h4
  have variants : m 8=9 ∨ m 8=16 := by
    rcases opts8 with e|e|e
    · exact (no h7 (by decide) e).elim
    · exact Or.inl e
    · exact Or.inr e
  rcases variants with h8|h8
  · have h9 := rev h8
    have h16 : m 16=17 := by
      rcases opts16 with e|e|e
      · exact (no h8 (by decide) e).elim
      · exact (no h15 (by decide) e).elim
      · exact e
    have h17 := rev h16
    have h13 : m 13=14 := by
      rcases opts13 with e|e|e
      · exact (no h12 (by decide) e).elim
      · exact e
      · exact (no h17 (by decide) e).elim
    have h14 := rev h13
    refine ⟨false,funext ?_⟩
    intro v
    fin_cases v
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17
  · have h16 := rev h8
    have h9 : m 9=14 := by
      rcases opts9 with e|e|e
      · exact (no h8 (by decide) e).elim
      · exact (no h10 (by decide) e).elim
      · exact e
    have h14 := rev h9
    have h17 : m 17=13 := by
      rcases opts17 with e|e|e
      · exact (no h0 (by decide) e).elim
      · exact e
      · exact (no h16 (by decide) e).elim
    have h13 := rev h17
    refine ⟨true,funext ?_⟩
    intro v
    fin_cases v
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17

theorem q_prescribed (t : Bool) : Prescribed (q t) :=
  ⟨q_inv t,q_adj t,by cases t <;> decide,
    fun i ni ei => ni ((q_omission t i).mp ei)⟩

theorem distinct_states : q false ≠ q true := by
  intro h
  exact (by decide : q false 8 ≠ q true 8) (congrFun h 8)

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


private theorem no_factor_closed_five (G : SimpleGraph Board) {S : Finset Board}
    (closed : Closed G S) (size : S.card=5) : ¬HasFactor G := by
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
  rw [eq,size] at card
  have cc : (∑ T∈Q,T.card) = Q.card * 3 := by
    rw [show (∑ T∈Q,T.card) = ∑ _T∈Q,(3:ℕ) from
      sum_congr rfl (fun T ht => (tiles' T (mem_filter.mp ht).1).1)]
    simp
  omega



def slot (i : Fin 6) : Port :=
  if i=0 then .inl (.inl false) else if i=1 then .inl (.inl true) else
  if i=2 then .inl (.inr false) else if i=3 then .inl (.inr true) else
  if i=4 then .inr false else .inr true

def decode (n : Nat) : Board := if n<18 then .inl (Fin.ofNat' 18 n) else .inr (slot (Fin.ofNat' 6 (n-18)))
def route (l : List Nat) : List Board := l.map decode


abbrev ranked (t : Bool) := rankOf (q t) (q_inv t)
theorem ranked_degree : ∀ t,∀ x,(ranked t).degree x=2 := by decide

/-- Exact union over all and only the matching ranks with one specified omission. -/
def prescribedUnion : SimpleGraph Board where
  Adj x y := ∃ m : Core→Core, ∃ p : Prescribed m, (rebuilt (rankOf m p.1)).Adj x y
  symm := by
    intro _ _ h
    obtain ⟨m,p,e⟩ := h
    exact ⟨m,p,e.symm⟩
  loopless := by
    intro x h
    obtain ⟨m,p,e⟩ := h
    exact (rebuilt (rankOf m p.1)).loopless x e

abbrev unionGraph := (rebuilt (ranked false)) ⊔ (rebuilt (ranked true))

instance : DecidableRel unionGraph.Adj := by
  intro x y
  change Decidable ((rebuilt (ranked false)).Adj x y ∨ (rebuilt (ranked true)).Adj x y)
  infer_instance

theorem union_exact : prescribedUnion = unionGraph := by
  ext x y
  change (∃ m : Core→Core, ∃ p : Prescribed m, (rebuilt (rankOf m p.1)).Adj x y) ↔
    ((rebuilt (ranked false)).Adj x y ∨ (rebuilt (ranked true)).Adj x y)
  constructor
  · rintro ⟨m,p,e⟩
    obtain ⟨t,h⟩ := classifies m p
    subst m
    cases t
    · exact Or.inl e
    · exact Or.inr e
  · rintro (a|b)
    · exact ⟨q false,q_prescribed false,a⟩
    · exact ⟨q true,q_prescribed true,b⟩

def oldShore : Finset Core := {2,3,4,5}

set_option maxRecDepth 8000 in
theorem forced_boundary :
    boundary core (fun x => decide (x∈oldShore)) =
      ({(2,1),(3,12),(4,15),(5,6)} : Finset (Core×Core)) := by
  ext e
  have tab : ∀ e : Core×Core,(e.1∈oldShore ∧ e.2∉oldShore ∧ core.Adj e.1 e.2) ↔
      e∈({(2,1),(3,12),(4,15),(5,6)} : Finset (Core×Core)) := by decide
  simpa [boundary] using tab e

set_option maxRecDepth 8000 in
theorem boundary_forced_in_all (m : Core→Core) (p : Prescribed m) :
    ∀ e ∈ boundary core (fun x => decide (x∈oldShore)), m e.1=e.2 := by
  obtain ⟨t,hm⟩ := classifies m p
  subst m
  rw [forced_boundary]
  cases t <;> decide

def smallRoute : List Board := route [2,3,4,5,20]
def largeRoute : List Board := route [1,21,6,7,8,9,18,10,11,12,23,13,14,19,15,16,17,0,22]

set_option maxRecDepth 8000 in
theorem union_geometry :
    smallRoute.Nodup ∧ largeRoute.Nodup ∧ smallRoute.length=5 ∧ largeRoute.length=19 ∧
    Closed unionGraph smallRoute.toFinset ∧ Closed unionGraph largeRoute.toFinset ∧
    Disjoint smallRoute.toFinset largeRoute.toFinset ∧
    smallRoute.toFinset ∪ largeRoute.toFinset = univ ∧
    smallRoute.Chain' unionGraph.Adj ∧ largeRoute.Chain' unionGraph.Adj := by decide

theorem union_closed : Closed prescribedUnion smallRoute.toFinset := by
  rw [union_exact]
  exact union_geometry.2.2.2.2.1

theorem union_no_factor : ¬HasFactor prescribedUnion := by
  apply no_factor_closed_five _ union_closed
  rw [List.toFinset_card_of_nodup union_geometry.1,union_geometry.2.2.1]

theorem union_disconnected : ¬prescribedUnion.Connected := by
  intro h
  have r : prescribedUnion.Reachable (decode 2) (decode 1) := h.preconnected _ _
  obtain ⟨w⟩ := r
  have preserve : ∀ {x y},prescribedUnion.Walk x y → x∈smallRoute.toFinset →
      y∈smallRoute.toFinset := by
    intro x y W hx
    induction W with
    | nil => exact hx
    | cons e rest ih => exact ih (union_closed _ _ hx e)
  exact (by decide : decode 1∉smallRoute.toFinset) (preserve w (by decide))

private def triple (a b c : Nat) : Finset Board := {decode a,decode b,decode c}
private def tiles : Finset (Finset Board) :=
  {triple 7 10 18,triple 1 6 21,triple 2 3 20,triple 4 5 15,
   triple 9 14 19,triple 8 16 17,triple 0 11 22,triple 12 13 23}

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




#print axioms classifies
#print axioms union_exact
#print axioms forced_boundary
#print axioms boundary_forced_in_all
#print axioms union_geometry
#print axioms union_no_factor
#print axioms union_disconnected
#print axioms unrestricted_factor
#print axioms host_three_connected
#print axioms exact_board
#print axioms wide
end KelmansCactus.AtomicBridge.SquareUnionLock
