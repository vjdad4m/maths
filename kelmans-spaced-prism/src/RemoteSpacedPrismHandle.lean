import HandleCuts
import RemoteSubdivisionCore
import RemoteT2CompletionTransfer

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSpacedPrismHandle
open HandleExtension (Edges)
open RemoteSubdivisionCore (Marks)
open RemoteT2CompletionTransfer (eraseEdge marked)
open SquareCap (SmallTrivial ThreeConnected)
noncomputable section
set_option linter.unusedSectionVars false

abbrev Port := (Bool⊕Bool)⊕Bool
abbrev V1 (V : Type*) := V⊕Bool
abbrev V2 (V : Type*) := V1 V⊕Bool
abbrev V3 (V : Type*) := V2 V⊕Bool
abbrev V4 (V : Type*) := V3 V⊕Bool

def first (s : Bool) : Port := .inl (.inl s)
def second (s : Bool) : Port := .inl (.inr s)
def third (s : Bool) : Port := .inr s

variable {V : Type*} {G : SimpleGraph V} (M : Marks G Port)

private theorem foreign (i j : Port) (ne : i≠j) : ¬M.Pair j (M.a i) (M.b i) := by
  intro h
  exact ne (M.slot_unique (show M.Pair i (M.a i) (M.b i) from Or.inl ⟨rfl,rfl⟩) h)

def pick1 : Edges G where
  a s := M.a (first s)
  b s := M.b (first s)
  edge s := M.edge (first s)
  separated h k := by simpa [first] using M.separated h k

def pick2 : Edges (pick1 M).host where
  a s := .inl (M.a (second s))
  b s := .inl (M.b (second s))
  edge s := by
    refine ⟨M.edge (second s),?_⟩
    rintro ⟨j,h⟩
    exact foreign M (second s) (first j) (by simp [first,second]) h
  separated := by
    intro s t x h k
    rcases h with h|h <;> rcases k with k|k
    all_goals have eq := h.symm.trans k
    all_goals simp only [Sum.inl.injEq] at eq
    · simpa [second] using M.separated (i:=second s) (j:=second t) (Or.inl rfl) (Or.inl eq)
    · simpa [second] using M.separated (i:=second s) (j:=second t) (Or.inl rfl) (Or.inr eq)
    · simpa [second] using M.separated (i:=second s) (j:=second t) (Or.inr rfl) (Or.inl eq)
    · simpa [second] using M.separated (i:=second s) (j:=second t) (Or.inr rfl) (Or.inr eq)

private def joinEnd (s t : Bool) : V2 V :=
  if s then .inr t else .inl (.inr t)

def pick3 : Edges (pick2 M).host where
  a s := joinEnd s false
  b s := joinEnd s true
  edge s := by
    cases s
    · change (false≠true) ∧ ¬(pick2 M).Removed (.inr false) (.inr true)
      simp [Edges.Removed,Edges.PairFor,pick2]
    · exact Bool.noConfusion
  separated := by
    intro s t x h k
    cases s <;> cases t
    all_goals first
      | rfl
      | rcases h with h|h <;> rcases k with k|k <;>
          have z := h.symm.trans k <;> simp [joinEnd] at z

def old2 (x : V) : V2 V := .inl (.inl x)
def old3 (x : V) : V3 V := .inl (old2 x)
def old (x : V) : V4 V := .inl (old3 x)

def pick4 : Edges (pick3 M).host where
  a s := old3 (M.a (third s))
  b s := old3 (M.b (third s))
  edge s := by
    refine ⟨⟨⟨M.edge (third s),?_⟩,?_⟩,?_⟩
    · rintro ⟨j,h⟩
      exact foreign M (third s) (first j) (by simp [first,third]) h
    · rintro ⟨j,h⟩
      have r : M.Pair (second j) (M.a (third s)) (M.b (third s)) := by
        simpa [Edges.PairFor,pick2] using h
      exact foreign M (third s) (second j) (by simp [second,third]) r
    · rintro ⟨j,h⟩
      cases j <;> simp [Edges.PairFor,pick3,joinEnd,old2] at h
  separated := by
    intro s t x h k
    rcases h with h|h <;> rcases k with k|k
    all_goals have eq := h.symm.trans k
    all_goals simp only [old3,old2,Sum.inl.injEq] at eq
    · simpa [third] using M.separated (i:=third s) (j:=third t) (Or.inl rfl) (Or.inl eq)
    · simpa [third] using M.separated (i:=third s) (j:=third t) (Or.inl rfl) (Or.inr eq)
    · simpa [third] using M.separated (i:=third s) (j:=third t) (Or.inr rfl) (Or.inl eq)
    · simpa [third] using M.separated (i:=third s) (j:=third t) (Or.inr rfl) (Or.inr eq)

abbrev Host : SimpleGraph (V4 V) := (pick4 M).host

def pole (s : Bool) : V4 V := .inl (.inr s)
def endFirst (s : Bool) : V4 V := .inl (.inl (.inl (.inr s)))
def endSecond (s : Bool) : V4 V := .inl (.inl (.inr s))
def endThird (s : Bool) : V4 V := .inr s

def embed : V⊕Port → V4 V
  | .inl v => old v
  | .inr (.inl (.inl s)) => endFirst s
  | .inr (.inl (.inr s)) => endSecond s
  | .inr (.inr s) => endThird s

theorem embed_injective : Function.Injective (embed (V:=V)) := by
  rintro (v|((s|s)|s)) (w|((t|t)|t)) eq <;>
    simp [embed,old,old2,old3,endFirst,endSecond,endThird] at eq ⊢ <;> assumption

theorem embed_range (z : V4 V) :
    z≠pole false ∧ z≠pole true ↔ ∃ w : V⊕Port,embed w=z := by
  rcases z with (((v|s)|s)|s)|s
  · exact ⟨fun _=>⟨.inl v,rfl⟩,fun _=>by simp [pole]⟩
  · exact ⟨fun _=>⟨.inr (first s),rfl⟩,fun _=>by simp [pole]⟩
  · exact ⟨fun _=>⟨.inr (second s),rfl⟩,fun _=>by simp [pole]⟩
  · cases s <;> simp [pole,embed,old,old2,old3,endFirst,endSecond,endThird]
  · exact ⟨fun _=>⟨.inr (third s),rfl⟩,fun _=>by simp [pole]⟩

theorem pole_join : (Host M).Adj (pole false) (pole true) := by
  simp [Host,Edges.host,Edges.deleteChosen,Edges.Removed,Edges.PairFor,pick4,old3,old2,pole]

theorem remote_edge : (Host M).Adj (endThird false) (endThird true) := by
  simp [Host,Edges.host,endThird]

theorem remote : RemoteT2Scope.Remote (Host M) (pole false) (endThird false) (endThird true) := by
  simp [RemoteT2Scope.Remote,Host,Edges.host,Edges.Ends,pick4,old3,old2,pole,endThird]

set_option maxHeartbeats 0 in
/-- Removing the two added poles and last joining edge gives exactly the
original core with the six independent edges subdivided. -/
theorem exact_survivor (u v : V⊕Port) :
    M.expanded.Adj u v ↔ (eraseEdge (Host M) (endThird false) (endThird true)).Adj (embed u) (embed v) := by
  rcases u with (a|((s|s)|s)) <;> rcases v with (b|((t|t)|t))
  all_goals try cases s <;> try cases t
  all_goals simp [Marks.expanded,Marks.Ends,Marks.Removed,Marks.Pair,embed,old,old2,old3,
    endFirst,endSecond,endThird,eraseEdge,marked,Host,pick1,pick2,pick3,pick4,joinEnd,
    Edges.host,Edges.deleteChosen,Edges.Removed,Edges.PairFor,Edges.Ends,first,second,third,
    Sum.exists,and_assoc,not_or]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem cubic (h : ∀ v,G.degree v=3) : ∀ v,(Host M).degree v=3 :=
  (pick4 M).cubic ((pick3 M).cubic ((pick2 M).cubic ((pick1 M).cubic h)))

theorem small_trivial (h : ∀ v,G.degree v=3) (s : SmallTrivial G) : SmallTrivial (Host M) := by
  have s1 := (pick1 M).preserves_small_trivial h (show FourRingCutAux.SmallTrivial G from s)
  have s2 := (pick2 M).preserves_small_trivial ((pick1 M).cubic h) s1
  have s3 := (pick3 M).preserves_small_trivial ((pick2 M).cubic ((pick1 M).cubic h)) s2
  exact (pick4 M).preserves_small_trivial ((pick3 M).cubic ((pick2 M).cubic ((pick1 M).cubic h))) s3

theorem order_card : Fintype.card (V4 V)=Fintype.card V+8 := by
  simp only [Fintype.card_sum,Fintype.card_bool]


#print axioms cubic
#print axioms small_trivial
end
end KelmansCactus.AtomicBridge.RemoteSpacedPrismHandle
