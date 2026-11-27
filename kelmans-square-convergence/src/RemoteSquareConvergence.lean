import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Sym.Sym2

namespace KelmansCactus.AtomicBridge.RemoteSquareConvergence
open SimpleGraph
open scoped Sym2
variable {V I S : Type*}

/-- A reach-preserving graph embedding on a fixed vertex type needs to preserve only
one-step adjacencies as arbitrary walks. -/
theorem lift_reach {X Y : SimpleGraph V}
    (h : ∀ ⦃x y⦄, X.Adj x y → Y.Reachable x y) {x y : V}
    (w : X.Reachable x y) : Y.Reachable x y := by
  obtain ⟨p⟩ := w
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons e _ ih => exact (h e).trans ih

def pair (a b x y : V) : Prop := (x=a ∧ y=b) ∨ (x=b ∧ y=a)

private theorem pair_symm {a b x y : V} (h : pair a b x y) : pair a b y x := by
  rcases h with h|h
  · exact Or.inr ⟨h.2,h.1⟩
  · exact Or.inl ⟨h.2,h.1⟩

private theorem pair_loop {a b x : V} (h : pair a b x x) : a=b := by
  rcases h with h|h
  · exact h.1.symm.trans h.2
  · exact h.2.symm.trans h.1

private theorem reach_pair {G : SimpleGraph V} {a b x y : V}
    (h : G.Reachable a b) (e : pair a b x y) : G.Reachable x y := by
  rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact h
  · exact h.symm

structure Quad (V : Type*) where
  a : V
  b : V
  c : V
  d : V
  ab : a≠b
  cd : c≠d
  ac : a≠c
  bd : b≠d

namespace Quad
def twist (q : Quad V) : Quad V := ⟨q.a,q.c,q.b,q.d,q.ac,q.bd,q.ab,q.cd⟩

def adj (q : Quad V) : Bool → V → V → Prop
  | false,x,y => pair q.a q.b x y ∨ pair q.c q.d x y
  | true,x,y => pair q.a q.c x y ∨ pair q.b q.d x y

theorem adj_symm (q : Quad V) (b : Bool) {x y : V}
    (h : q.adj b x y) : q.adj b y x := by
  cases b <;> exact h.elim (fun e => Or.inl (pair_symm e)) (fun e => Or.inr (pair_symm e))

theorem adj_loopless (q : Quad V) (b : Bool) (x : V) : ¬q.adj b x x := by
  cases b
  · exact fun h=>h.elim (fun e=>q.ab (pair_loop e)) (fun e=>q.cd (pair_loop e))
  · exact fun h=>h.elim (fun e=>q.ac (pair_loop e)) (fun e=>q.bd (pair_loop e))

def orient (q : Quad V) : Bool → Quad V
  | false => q
  | true => q.twist

theorem adj_orient_old (q : Quad V) (t : Bool) (x y : V) :
    q.adj t x y ↔
      pair (q.orient t).a (q.orient t).b x y ∨ pair (q.orient t).c (q.orient t).d x y := by
  cases t <;> rfl

theorem adj_orient_new (q : Quad V) (t : Bool) (x y : V) :
    q.adj (!t) x y ↔
      pair (q.orient t).a (q.orient t).c x y ∨ pair (q.orient t).b (q.orient t).d x y := by
  cases t <;> rfl

end Quad

def network (B : SimpleGraph V) (gate : I→Quad V) (s : I → Bool) : SimpleGraph V where
  Adj x y := B.Adj x y ∨ ∃ i, (gate i).adj (s i) x y
  symm := by
    rintro x y (h|⟨i,h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨i,(gate i).adj_symm (s i) h⟩
  loopless := by
    rintro x (h|⟨i,h⟩)
    · exact B.loopless x h
    · exact (gate i).adj_loopless (s i) x h

def unionNetwork (B : SimpleGraph V) (gate : I→Quad V) : SimpleGraph V where
  Adj x y := B.Adj x y ∨ ∃ i b, (gate i).adj b x y
  symm := by
    rintro x y (h|⟨i,b,h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨i,b,(gate i).adj_symm b h⟩
  loopless := by
    rintro x (h|⟨i,b,h⟩)
    · exact B.loopless x h
    · exact (gate i).adj_loopless b x h

def without (B : SimpleGraph V) (gate : I→Quad V) (s : I→Bool) (i : I) : SimpleGraph V where
  Adj x y := B.Adj x y ∨ ∃ j, j≠i ∧ (gate j).adj (s j) x y
  symm := by
    rintro x y (h|⟨j,ne,h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨j,ne,(gate j).adj_symm (s j) h⟩
  loopless := by
    rintro x (h|⟨j,_,h⟩)
    · exact B.loopless x h
    · exact (gate j).adj_loopless (s j) x h

theorem network_le_union (B : SimpleGraph V) (gate : I→Quad V) (s : I→Bool) :
    network B gate s ≤ unionNetwork B gate := by
  rintro x y (e|⟨i,e⟩)
  · exact Or.inl e
  · exact Or.inr ⟨i,s i,e⟩

def flip [DecidableEq I] (s : I→Bool) (i : I) (j : I) : Bool :=
  if j=i then !(s j) else s j

theorem without_le_flip [DecidableEq I] (B : SimpleGraph V)
    (gate : I→Quad V) (s : I→Bool) (i : I) :
    without B gate s i ≤ network B gate (flip s i) := by
  rintro x y (e|⟨j,hj,e⟩)
  · exact Or.inl e
  · exact Or.inr ⟨j,by simpa [flip,hj] using e⟩

theorem present_edges (B : SimpleGraph V) (gate : I→Quad V) (s : I→Bool) (i : I) :
    let q := (gate i).orient (s i)
    (network B gate s).Adj q.a q.b ∧ (network B gate s).Adj q.c q.d := by
  dsimp only
  constructor
  · exact Or.inr ⟨i,((gate i).adj_orient_old (s i) _ _).2 (Or.inl (Or.inl ⟨rfl,rfl⟩))⟩
  · exact Or.inr ⟨i,((gate i).adj_orient_old (s i) _ _).2 (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩

theorem flip_adjacent [DecidableEq I] (B : SimpleGraph V) (gate : I→Quad V)
    (s : I→Bool) (i : I) {x y : V} (h : (gate i).adj (!(s i)) x y) :
    (network B gate (flip s i)).Adj x y :=
  Or.inr ⟨i,by simpa [flip] using h⟩

theorem flip_preserves_reach [DecidableEq I] (B : SimpleGraph V)
    (gate : I→Quad V) (s : I→Bool) (i : I)
    (ha : (without B gate s i).Reachable ((gate i).orient (s i)).a ((gate i).orient (s i)).b)
    (hc : (without B gate s i).Reachable ((gate i).orient (s i)).c ((gate i).orient (s i)).d)
    {x y : V} (e : (network B gate s).Reachable x y) :
    (network B gate (flip s i)).Reachable x y := by
  apply lift_reach _ e
  rintro u v (e|⟨j,e⟩)
  · exact SimpleGraph.Adj.reachable (G:=network B gate (flip s i)) (Or.inl e)
  by_cases eq : j=i
  · subst j
    rcases ((gate i).adj_orient_old (s i) _ _).1 e with e|e
    · exact reach_pair (ha.mono (without_le_flip B gate s i)) e
    · exact reach_pair (hc.mono (without_le_flip B gate s i)) e
  · exact SimpleGraph.Adj.reachable (G:=network B gate (flip s i)) (Or.inr ⟨j,by simpa [flip,eq] using e⟩)

/-- It suffices to bypass each of the present pairs whenever a square straddles
two current components. In cubic rank applications, the bypasses come from the
two old 2-factor cycles. -/
def CanBypass (B : SimpleGraph V) (gate : I→Quad V) : Prop :=
  ∀ s i, let q := (gate i).orient (s i)
    ¬ (network B gate s).Reachable q.a q.c →
    (without B gate s i).Reachable q.a q.b ∧ (without B gate s i).Reachable q.c q.d

theorem frontier [DecidableEq I] (B : SimpleGraph V) (gate : I→Quad V)
    (ok : CanBypass B gate) (s : I→Bool) {x y : V}
    (e : (unionNetwork B gate).Adj x y) (missing : ¬(network B gate s).Reachable x y) :
    ∃ i, ¬ (network B gate s).Reachable ((gate i).orient (s i)).a ((gate i).orient (s i)).c ∧
      (∀ u v, (network B gate s).Reachable u v →
                    (network B gate (flip s i)).Reachable u v) ∧
      (network B gate (flip s i)).Adj x y := by
  rcases e with e|⟨i,t,e⟩
  · exact (missing (SimpleGraph.Adj.reachable (G:=network B gate s) (Or.inl e))).elim
  have ht : t= !(s i) := by
    cases hi : s i <;> cases t <;> simp at *
    · exact (missing (SimpleGraph.Adj.reachable (G:=network B gate s) (Or.inr ⟨i,hi ▸ e⟩))).elim
    · exact (missing (SimpleGraph.Adj.reachable (G:=network B gate s) (Or.inr ⟨i,hi ▸ e⟩))).elim
  subst t
  rcases present_edges B gate s i with ⟨ea,ec⟩
  have sep : ¬ (network B gate s).Reachable ((gate i).orient (s i)).a ((gate i).orient (s i)).c := by
    intro h
    rcases ((gate i).adj_orient_new (s i) _ _).1 e with l|r
    · exact missing (reach_pair h l)
    · exact missing (reach_pair (ea.reachable.symm.trans (h.trans ec.reachable)) r)
  rcases ok s i sep with ⟨ha,hc⟩
  exact ⟨i,sep,fun _ _ => flip_preserves_reach B gate s i ha hc,flip_adjacent B gate s i e⟩

/-- Number of ordered pairs in the same component (including the diagonal). -/
noncomputable def reachPairs [Fintype V] (G : SimpleGraph V) : Finset (V×V) := by
  classical
  exact Finset.univ.filter (fun p => G.Reachable p.1 p.2)

theorem mem_reachPairs [Fintype V] {G : SimpleGraph V} {x y : V} :
    (x,y) ∈ reachPairs G ↔ G.Reachable x y := by
  classical
  simp [reachPairs]

theorem measure_grows [Fintype V] {X Y : SimpleGraph V}
    (inc : ∀ u v, X.Reachable u v → Y.Reachable u v)
    {x y : V} (new : Y.Reachable x y) (old : ¬X.Reachable x y) :
    (reachPairs X).card < (reachPairs Y).card := by
  classical
  refine Finset.card_lt_card ⟨?_,?_⟩
  · rintro ⟨u,v⟩ h
    exact mem_reachPairs.mpr (inc _ _ (mem_reachPairs.mp h))
  · intro h
    exact old (mem_reachPairs.mp (h (mem_reachPairs.mpr new)))

/-- A finite reachability measure gives actual convergence from each initial state,
not merely the existence of an optimal state. The state space may even be infinite. -/
theorem convergence [Fintype V] (F : S→SimpleGraph V) (U : SimpleGraph V)
    (step : S→S→Prop) (sub : ∀ s,F s≤U)
    (front : ∀ s x y, U.Adj x y → ¬(F s).Reachable x y →
      ∃ t, step s t ∧ (∀ u v,(F s).Reachable u v → (F t).Reachable u v) ∧
        (F t).Reachable x y) (start : S) :
    ∃ final, Relation.ReflTransGen step start final ∧
      ∀ x y, (F final).Reachable x y ↔ U.Reachable x y := by
  classical
  let μ (s : S) := Fintype.card (V×V) - (reachPairs (F s)).card
  suffices out : ∀ n s, μ s=n →
      ∃ final, Relation.ReflTransGen step s final ∧
        ∀ x y, (F final).Reachable x y ↔ U.Reachable x y by
    exact out (μ start) start rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s eq
    by_cases h : ∀ x y, U.Adj x y → (F s).Reachable x y
    · exact ⟨s,.refl,fun x y=>⟨fun w=>w.mono (sub s),lift_reach (fun {u v}=>h u v)⟩⟩
    push_neg at h
    rcases h with ⟨x,y,e,missing⟩
    rcases front s x y e missing with ⟨t,st,inc,w⟩
    have bound : (reachPairs (F t)).card ≤ Fintype.card (V×V) := Finset.card_le_univ _
    have lt : μ t<n := by
      rw [←eq]
      dsimp only [μ]
      have grow := measure_grows inc w missing
      omega
    rcases ih _ lt t rfl with ⟨f,path,done⟩
    exact ⟨f,(Relation.ReflTransGen.single st).trans path,done⟩

/-- Turn any compatible starting orientation into one with the exact components of
the union of both choices. Every chosen switch crosses a current component frontier. -/
theorem square_convergence [Fintype V] [DecidableEq I] (B : SimpleGraph V)
    (gate : I→Quad V) (ok : CanBypass B gate) (start : I→Bool) :
    ∃ final,
      Relation.ReflTransGen (fun s t=> ∃ i, t=flip s i ∧
        ¬(network B gate s).Reachable ((gate i).orient (s i)).a ((gate i).orient (s i)).c)
        start final ∧
      ∀ x y, (network B gate final).Reachable x y ↔ (unionNetwork B gate).Reachable x y := by
  apply convergence (network B gate) (unionNetwork B gate) _ (network_le_union B gate) _ start
  intro s x y e missing
  rcases frontier B gate ok s e missing with ⟨i,sep,inc,new⟩
  exact ⟨flip s i,⟨i,rfl,sep⟩,inc,new.reachable⟩


/-- A path constrained by its current old component can be transferred edge by edge. -/
theorem lift_reach_from_root {X D K : SimpleGraph V} (sub : D≤X) {a b : V}
    (path : D.Reachable a b)
    (h : ∀ u v, X.Reachable a u → D.Adj u v → K.Adj u v) :
    K.Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at path
  induction path with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u v p e ih =>
    have reach : D.Reachable a u := (SimpleGraph.reachable_iff_reflTransGen (G:=D) _ _).2 p
    exact ih.trans (h _ _ (reach.mono sub) e).reachable

theorem pair_deleted {G : SimpleGraph V} {a b x y : V}
    (d : (G.deleteEdges {s(a,b)}).Adj x y) : ¬ pair a b x y := by
  intro h
  have e := (SimpleGraph.deleteEdges_adj.mp d).2
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact e (by simp)
  · exact e (by simp [Sym2.eq_swap])

/-- The real geometric bypass input is just that present gate edges are not
bridges. The alternate path for one cannot use the other when the gate has
two different current components. -/
theorem bypass_of_alternate (B : SimpleGraph V) (gate : I→Quad V)
    (alt : ∀ s i, let q := (gate i).orient (s i)
      ((network B gate s).deleteEdges {s(q.a,q.b)}).Reachable q.a q.b ∧
      ((network B gate s).deleteEdges {s(q.c,q.d)}).Reachable q.c q.d) :
    CanBypass B gate := by
  intro s i
  dsimp only
  intro sep
  rcases alt s i with ⟨pa,pc⟩
  rcases present_edges B gate s i with ⟨hab,hcd⟩
  let q := (gate i).orient (s i)
  have route :
      ∀ {e f u v : V}, ¬(network B gate s).Reachable e u →
        (network B gate s).Reachable u v →
        (∀ x y, (gate i).adj (s i) x y → pair e f x y ∨ pair u v x y) →
        ((network B gate s).deleteEdges {s(e,f)}).Reachable e f →
        (without B gate s i).Reachable e f := by
    intro e f u v nr uv split P
    apply lift_reach_from_root ((network B gate s).deleteEdges_le _) P
    intro x y rx xy
    rcases (SimpleGraph.deleteEdges_adj.mp xy).1 with h|⟨j,h⟩
    · exact Or.inl h
    by_cases eq : j=i
    · subst j
      rcases split _ _ h with h|h
      · exact (pair_deleted xy h).elim
      · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (nr rx).elim
        · exact (nr (rx.trans uv.symm)).elim
    · exact Or.inr ⟨j,eq,h⟩
  constructor
  · exact route (e:=q.a) (f:=q.b) (u:=q.c) (v:=q.d)
      sep hcd.reachable (fun x y => ((gate i).adj_orient_old (s i) x y).1) pa
  · exact route (e:=q.c) (f:=q.d) (u:=q.a) (v:=q.b)
      (fun h=>sep h.symm) hab.reachable
      (fun x y h => (((gate i).adj_orient_old (s i) x y).1 h).symm) pc

theorem bypass_of_cycles (B : SimpleGraph V) (gate : I→Quad V)
    (cyc : ∀ s i, let q := (gate i).orient (s i)
      (∃ (u : V) (w : (network B gate s).Walk u u), w.IsCycle ∧ s(q.a,q.b)∈w.edges) ∧
      (∃ (u : V) (w : (network B gate s).Walk u u), w.IsCycle ∧ s(q.c,q.d)∈w.edges)) :
    CanBypass B gate := by
  apply bypass_of_alternate
  intro s i
  rcases cyc s i with ⟨c1,c2⟩
  exact ⟨(SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mpr c1).2,
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mpr c2).2⟩

#print axioms KelmansCactus.AtomicBridge.RemoteSquareConvergence.bypass_of_cycles
#print axioms KelmansCactus.AtomicBridge.RemoteSquareConvergence.square_convergence

end KelmansCactus.AtomicBridge.RemoteSquareConvergence
