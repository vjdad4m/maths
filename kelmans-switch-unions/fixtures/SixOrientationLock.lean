import RemoteSpacedPrismLayout
import RemoteCutCertificate
import RemoteSpacedPrismWidth
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Chain

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.SixOrientationLock
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide ThreeConnected boundary HasFactor FactorOn IsTile)

abbrev Core := Fin 18

def succ (v : Core) : Core := ⟨(v.val+1)%18,Nat.mod_lt _ (by decide)⟩

def mate (v : Core) : Core :=
  ([11, 8, 6, 15, 13, 9, 2, 16, 1, 5, 14, 0, 17, 4, 10, 3, 7, 12] : List Core)[v.val]!

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
  | .inl (.inl false) => 2
  | .inl (.inl true) => 0
  | .inl (.inr false) => 15
  | .inl (.inr true) => 11
  | .inr false => 4
  | .inr true => 10

def b : Port → Core
  | .inl (.inl false) => 3
  | .inl (.inl true) => 17
  | .inl (.inr false) => 16
  | .inl (.inr true) => 12
  | .inr false => 13
  | .inr true => 14

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
  edges := [(0, 1), (0, 11), (0, 17), (1, 2), (1, 8), (2, 3), (2, 6), (3, 4), (3, 15), (4, 5), (4, 13), (5, 6), (5, 9), (6, 7), (7, 8), (7, 16), (8, 9), (9, 10), (10, 11), (10, 14), (11, 12), (12, 13), (12, 17), (13, 14), (14, 15), (15, 16), (16, 17)]
  sorted := by decide
  nodup := by decide

private theorem table_eq : edgeTable.graph = core := by
  ext x y
  have all : ∀ x y : Core, edgeTable.graph.Adj x y ↔ core.Adj x y := by decide
  exact all x y

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem table_valid :
    edgeTable.cert 4 1 [10,9,5,4,13,3,15,2,6,1,8,7,16,0,11,12,17]
      (RemoteCutCertificate.Table.base 14)=true := by decide

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
  (if t then [17, 8, 6, 4, 3, 9, 2, 16, 1, 5, 11, 10, 13, 12, 15, 14, 7, 0] else [17, 2, 1, 4, 3, 6, 5, 16, 9, 8, 11, 10, 13, 12, 15, 14, 7, 0] : List Core)[v.val]!
theorem q_inv (t : Bool) : Function.Involutive (q t) := by
  change ∀ v : Core,q t (q t v)=v
  cases t <;> decide

theorem q_adj : ∀ t (v : Core),core.Adj v (q t v) := by decide

def omitted : Port := .inl (.inl true)
theorem q_omission : ∀ t (i : Port),(q t (a i)=b i) ↔ i=omitted := by decide

def Prescribed (m : Core→Core) : Prop :=
  Function.Involutive m ∧
  (∀ v,core.Adj v (m v)) ∧ m 0=17 ∧
  (∀ i : Port,i≠omitted → m (a i)≠b i)

theorem classifies (m : Core→Core) (P : Prescribed m) :
    ∃ t : Bool,m = q t := by
  obtain ⟨inv,adj,h0,avoid⟩ := P
  have rev {u v : Core} (e : m u=v) : m v=u := by rw [←e,inv]
  have no {u v w : Core} (h : m v=w) (ne : u≠w) : m u≠v :=
    fun e=>ne ((rev e).symm.trans h)
  have h17 := rev h0
  have opts1 : m 1=0 ∨ m 1=2 ∨ m 1=8 := by
    have h : ∀ w : Core,core.Adj 1 w → w=0 ∨ w=2 ∨ w=8 := by decide
    exact h _ (adj 1)
  have opts2 : m 2=1 ∨ m 2=3 ∨ m 2=6 := by
    have h : ∀ w : Core,core.Adj 2 w → w=1 ∨ w=3 ∨ w=6 := by decide
    exact h _ (adj 2)
  have opts3 : m 3=2 ∨ m 3=4 ∨ m 3=15 := by
    have h : ∀ w : Core,core.Adj 3 w → w=2 ∨ w=4 ∨ w=15 := by decide
    exact h _ (adj 3)
  have opts5 : m 5=4 ∨ m 5=6 ∨ m 5=9 := by
    have h : ∀ w : Core,core.Adj 5 w → w=4 ∨ w=6 ∨ w=9 := by decide
    exact h _ (adj 5)
  have opts6 : m 6=2 ∨ m 6=5 ∨ m 6=7 := by
    have h : ∀ w : Core,core.Adj 6 w → w=2 ∨ w=5 ∨ w=7 := by decide
    exact h _ (adj 6)
  have opts8 : m 8=1 ∨ m 8=7 ∨ m 8=9 := by
    have h : ∀ w : Core,core.Adj 8 w → w=1 ∨ w=7 ∨ w=9 := by decide
    exact h _ (adj 8)
  have opts11 : m 11=0 ∨ m 11=10 ∨ m 11=12 := by
    have h : ∀ w : Core,core.Adj 11 w → w=0 ∨ w=10 ∨ w=12 := by decide
    exact h _ (adj 11)
  have opts12 : m 12=11 ∨ m 12=13 ∨ m 12=17 := by
    have h : ∀ w : Core,core.Adj 12 w → w=11 ∨ w=13 ∨ w=17 := by decide
    exact h _ (adj 12)
  have opts14 : m 14=10 ∨ m 14=13 ∨ m 14=15 := by
    have h : ∀ w : Core,core.Adj 14 w → w=10 ∨ w=13 ∨ w=15 := by decide
    exact h _ (adj 14)
  have opts16 : m 16=7 ∨ m 16=15 ∨ m 16=17 := by
    have h : ∀ w : Core,core.Adj 16 w → w=7 ∨ w=15 ∨ w=17 := by decide
    exact h _ (adj 16)
  have h11 : m 11=10 := by
    rcases opts11 with e|e|e
    · exact (no h0 (by decide) e).elim
    · exact e
    · exact (avoid (.inl (.inr true)) (by decide) e).elim
  have h10 := rev h11
  have h12 : m 12=13 := by
    rcases opts12 with e|e|e
    · exact (no h11 (by decide) e).elim
    · exact e
    · exact (no h17 (by decide) e).elim
  have h13 := rev h12
  have h14 : m 14=15 := by
    rcases opts14 with e|e|e
    · exact (no h10 (by decide) e).elim
    · exact (no h13 (by decide) e).elim
    · exact e
  have h15 := rev h14
  have h3 : m 3=4 := by
    rcases opts3 with e|e|e
    · exact (avoid (.inl (.inl false)) (by decide) (rev e)).elim
    · exact e
    · exact (no h15 (by decide) e).elim
  have h4 := rev h3
  have h16 : m 16=7 := by
    rcases opts16 with e|e|e
    · exact e
    · exact (no h15 (by decide) e).elim
    · exact (no h17 (by decide) e).elim
  have h7 := rev h16
  have variants : m 1=2 ∨ m 1=8 := by
    rcases opts1 with e|e|e
    · exact (no h0 (by decide) e).elim
    · exact Or.inl e
    · exact Or.inr e
  rcases variants with h1|h1
  · have h2 := rev h1
    have h6 : m 6=5 := by
      rcases opts6 with e|e|e
      · exact (no h2 (by decide) e).elim
      · exact e
      · exact (no h7 (by decide) e).elim
    have h5 := rev h6
    have h8 : m 8=9 := by
      rcases opts8 with e|e|e
      · exact (no h1 (by decide) e).elim
      · exact (no h7 (by decide) e).elim
      · exact e
    have h9 := rev h8
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
  · have h8 := rev h1
    have h2 : m 2=6 := by
      rcases opts2 with e|e|e
      · exact (no h1 (by decide) e).elim
      · exact (no h3 (by decide) e).elim
      · exact e
    have h6 := rev h2
    have h5 : m 5=9 := by
      rcases opts5 with e|e|e
      · exact (no h4 (by decide) e).elim
      · exact (no h6 (by decide) e).elim
      · exact e
    have h9 := rev h5
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
  exact (by decide : q false 1 ≠ q true 1) (congrFun h 1)

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


def smallRoute (t : Bool) : List Board := route
  (if t then [4,5,6,7,8,9,10,23,14,13,22] else [4,5,9,10,23,14,13,22])
def largeRoute (t : Bool) : List Board := route
  (if t then [1,2,18,3,15,20,16,17,12,21,11,0,19]
   else [1,8,7,6,2,18,3,15,20,16,17,12,21,11,0,19])

set_option maxRecDepth 8000 in
theorem rank_geometry (t : Bool) :
    (smallRoute t).Nodup ∧ (largeRoute t).Nodup ∧
    (smallRoute t).length=(if t then 11 else 8) ∧ (largeRoute t).length=(if t then 13 else 16) ∧
    Closed (rebuilt (ranked t)) (smallRoute t).toFinset ∧
    Closed (rebuilt (ranked t)) (largeRoute t).toFinset ∧
    Disjoint (smallRoute t).toFinset (largeRoute t).toFinset ∧
    (smallRoute t).toFinset ∪ (largeRoute t).toFinset=univ ∧
    (smallRoute t).Chain' (rebuilt (ranked t)).Adj ∧ (largeRoute t).Chain' (rebuilt (ranked t)).Adj := by
  cases t <;> decide

theorem rank_no_factor (t : Bool) : ¬HasFactor (rebuilt (ranked t)) := by
  have g := rank_geometry t
  apply no_factor_closed_mod _ g.2.2.2.2.1
  rw [List.toFinset_card_of_nodup g.1,g.2.2.1]
  cases t <;> decide

theorem no_prescribed_factor (m : Core→Core) (h : Prescribed m) :
    ¬HasFactor (rebuilt (rankOf m h.1)) := by
  obtain ⟨t,e⟩ := classifies m h
  subst m
  exact rank_no_factor t

theorem exactly_six_exchange :
    ∀ x y : Core, ((q false x=y ∧ q true x≠y) ∨ (q true x=y ∧ q false x≠y)) ↔
      let L : List (Core×Core) := [(6,2),(2,1),(1,8),(8,9),(9,5),(5,6)]
      (x,y)∈L ∨ (y,x)∈L := by decide

theorem six_alternates :
    (ranked false).Adj 6 2 ∧ (ranked false).Adj 1 8 ∧ (ranked false).Adj 9 5 ∧
    (ranked true).Adj 2 1 ∧ (ranked true).Adj 8 9 ∧ (ranked true).Adj 5 6 := by decide

def unionRoute : List Board := route [4,22,13,14,23,10,9,5,6,7,8,1,2,18,3,15,20,16,17,12,21,11,0,19]
theorem union_route :
    unionRoute.Nodup ∧ unionRoute.length=24 ∧ unionRoute.toFinset=univ ∧
      unionRoute.Chain' unionGraph.Adj := by decide

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

theorem union_connected : prescribedUnion.Connected := by
  rw [union_exact]
  apply (SimpleGraph.connected_iff_exists_forall_reachable unionGraph).mpr
  refine ⟨decode 4,?_⟩
  intro x
  apply reach_of_route (route [22,13,14,23,10,9,5,6,7,8,1,2,18,3,15,20,16,17,12,21,11,0,19])
  · exact union_route.2.2.2
  · have hx : x∈unionRoute.toFinset := by rw [union_route.2.2.1]; exact mem_univ _
    exact List.mem_toFinset.mp hx

private def triple (a b c : Nat) : Finset Board := {decode a,decode b,decode c}
private def tiles : Finset (Finset Board) :=
  {triple 4 22 13,triple 14 23 10,triple 9 5 6,triple 7 8 1,
   triple 2 18 3,triple 15 20 16,triple 17 12 21,triple 11 0 19}

theorem union_factor : HasFactor prescribedUnion := by
  rw [union_exact]
  refine ⟨tiles,?_,?_,?_⟩
  · change ∀ A ∈ tiles,A.card=3 ∧ ∃ c∈A,∀ x∈A,x≠c → unionGraph.Adj c x
    decide
  · decide
  · decide

private def unrestrictedTiles : Finset (Finset Board) :=
  {triple 1 2 18,triple 11 0 19,triple 13 12 21,triple 17 16 20,
   triple 3 4 22,triple 15 14 23,triple 8 9 10,triple 5 6 7}

theorem unrestricted_factor : HasFactor board := by
  refine ⟨unrestrictedTiles,?_,?_,?_⟩
  · change ∀ A ∈ unrestrictedTiles,A.card=3 ∧ ∃ c∈A,∀ x∈A,x≠c → board.Adj c x
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
#print axioms exactly_six_exchange
#print axioms rank_geometry
#print axioms no_prescribed_factor
#print axioms union_connected
#print axioms union_factor
#print axioms unrestricted_factor
#print axioms host_three_connected
#print axioms exact_board
#print axioms wide
end KelmansCactus.AtomicBridge.SixOrientationLock
