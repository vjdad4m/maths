import RemotePairStrip
import RemoteBudgetExpectation
import Mathlib.Tactic.FinCases

namespace KelmansCactus.AtomicBridge.RemoteSquareBudgetConditional
open SimpleGraph Finset
open scoped BigOperators
open RemoteBudgetComponent (Mate cost)
open RemoteRankUnion (Marking)
open RemotePairStrip (Strip Closed one_cost_bound two_cost_bound)
variable {V I : Type*} {G : SimpleGraph V}

def SquareAdjacent (i j : Fin 4) : Prop :=
  (i.val+1)%4=j.val ∨ (j.val+1)%4=i.val

instance (i j : Fin 4) : Decidable (SquareAdjacent i j) := by
  unfold SquareAdjacent
  infer_instance

structure Square (p : Mate G) where
  corner : Fin 4 → V
  distinct : Function.Injective corner
  edges : ∀ i j,SquareAdjacent i j → G.Adj (corner i) (corner j)
  external : ∀ i j,p.mate (corner i)≠corner j
  only : ∀ i x,G.Adj (corner i) x →
    x=p.mate (corner i) ∨ ∃ j,SquareAdjacent i j ∧ x=corner j

namespace Square
variable {p : Mate G} (A : Square p)

def openPort (q : Mate G) (i : Fin 4) : Prop :=
  q.mate (A.corner i)≠p.mate (A.corner i)

noncomputable def lost (q : Mate G) : ℕ := by
  classical
  exact (Finset.univ.filter (A.openPort q)).card

def NoDiagonal : Prop :=
  ∀ i j k l : Fin 4, i≠j → k≠l →
    ¬SquareAdjacent i j → ¬SquareAdjacent k l →
    ∀ (W : G.Walk (p.mate (A.corner i)) (p.mate (A.corner j)))
      (X : G.Walk (p.mate (A.corner k)) (p.mate (A.corner l))),
      (∀ x∈W.support,∀ t,x≠A.corner t) →
      (∀ x∈X.support,∀ t,x≠A.corner t) →
      (∀ x∈W.support,x∉X.support) → False

structure OutsideStrip (q : Mate G) (i j : Fin 4) where
  strip : Strip p q (A.corner i) (A.corner j)
  outside : ∀ x∈strip.region,∀ t,x≠A.corner t
  link : G.Walk (p.mate (A.corner i)) (p.mate (A.corner j))
  link_in : ∀ x∈link.support,x∈strip.region

structure FourDistinct (i j k l : Fin 4) : Prop where
  ij : i≠j
  ik : i≠k
  il : i≠l
  jk : j≠k
  jl : j≠l
  kl : k≠l

theorem adjacent_eq_pairing : ∀ i j k l, FourDistinct i j k l →
    (SquareAdjacent i j ↔ SquareAdjacent k l) := by
  have e : ∀ i j k l : Fin 4, i≠j → i≠k → i≠l → j≠k → j≠l → k≠l →
      (SquareAdjacent i j ↔ SquareAdjacent k l) := by decide
  intro i j k l h
  exact e i j k l h.ij h.ik h.il h.jk h.jl h.kl

theorem four_cover : ∀ i j k l, FourDistinct i j k l →
    ∀ x : Fin 4,x=i∨x=j∨x=k∨x=l := by
  have e : ∀ i j k l : Fin 4, i≠j → i≠k → i≠l → j≠k → j≠l → k≠l →
      ∀ x : Fin 4,x=i∨x=j∨x=k∨x=l := by decide
  intro i j k l h
  exact e i j k l h.ij h.ik h.il h.jk h.jl h.kl

theorem nondiagonal_pairs {q : Mate G} {i j k l : Fin 4}
    (h : FourDistinct i j k l) (one : A.OutsideStrip q i j) (two : A.OutsideStrip q k l)
    (disjoint : ∀ x∈one.strip.region,x∉two.strip.region) (no : A.NoDiagonal) :
    SquareAdjacent i j ∧ SquareAdjacent k l := by
  have eq := adjacent_eq_pairing i j k l h
  by_cases good : SquareAdjacent i j
  · exact ⟨good,eq.mp good⟩
  exfalso
  exact no i j k l h.ij h.kl good (fun t=>good (eq.mpr t)) one.link two.link
    (fun x hx=>one.outside x (one.link_in x hx))
    (fun x hx=>two.outside x (two.link_in x hx))
    (fun x hx h2=>disjoint x (one.link_in x hx) (two.link_in x h2))

theorem lost_none {q : Mate G} (none : ∀ x,¬A.openPort q x) : A.lost q=0 := by
  classical
  have h : Finset.univ.filter (A.openPort q)=∅ := by
    ext i
    simp [none i]
  simp [lost,h]

theorem lost_two {q : Mate G} {i j : Fin 4} (ne : i≠j)
    (opened : ∀ x,A.openPort q x ↔ x=i∨x=j) : A.lost q=2 := by
  classical
  have shape : Finset.univ.filter (A.openPort q) = {i,j} := by
    ext x
    simp [opened x]
  rw [lost,shape]
  simp [ne]

theorem lost_four {q : Mate G} (opened : ∀ i,A.openPort q i) : A.lost q=4 := by
  classical
  have h : Finset.univ.filter (A.openPort q)=Finset.univ := by
    ext i
    simp [opened i]
  simp [lost,h]

theorem q_pairs_two {q : Mate G} {i j : Fin 4}
    (opened : ∀ x,A.openPort q x ↔ x=i∨x=j) :
    q.mate (A.corner i)=A.corner j := by
  have e := A.only i _ (q.edge (A.corner i))
  rcases e with cut|⟨k,_,other⟩
  · exact (((opened i).mpr (Or.inl rfl)) cut).elim
  have qi : q.mate (A.corner k)=A.corner i := Mate.reverse other
  have open_k : A.openPort q k := fun stay=>A.external k i (stay.symm.trans qi)
  rcases (opened k).mp open_k with e|e
  · rw [e] at other
    have adj := q.edge (A.corner i)
    rw [other] at adj
    exact (G.loopless _ adj).elim
  · rwa [e] at other

theorem release_opens {q : Mate G} {i j : Fin 4} (S : A.OutsideStrip q i j)
    (ab : G.Adj (A.corner i) (A.corner j)) :
    ∀ t,A.openPort (S.strip.release ab) t ↔ t=i∨t=j := by
  intro t
  constructor
  · intro h
    by_contra! no
    apply h
    apply S.strip.release_old_out ab
    intro mem
    rcases mem with r|e|e
    · exact S.outside _ r t rfl
    · exact no.1 (A.distinct e)
    · exact no.2 (A.distinct e)
  · rintro (rfl|rfl)
    · exact S.strip.release_changes_a ab
    · exact S.strip.release_changes_b ab

end Square

/-- Target matching geometry is explicit: no edges lost, one exterior strip,
or two genuinely disjoint exterior strips. A matching decomposition theorem
would supply these inputs; the arithmetic below does not assume it silently. -/
inductive Decomposition {p : Mate G} (A : Square p) (q : Mate G) : Type _
  | none (noneOpened : ∀ t,¬A.openPort q t)
  | two (i j : Fin 4) (ne : i≠j) (opened : ∀ t,A.openPort q t ↔ t=i∨t=j)
      (S : A.OutsideStrip q i j)
  | four (i j k l : Fin 4) (distinct : Square.FourDistinct i j k l)
      (opened : ∀ t,A.openPort q t)
      (S : A.OutsideStrip q i j) (T : A.OutsideStrip q k l)
      (apart : ∀ x∈S.strip.region,x∉T.strip.region)

structure Row [Fintype I] (M : Marking G I) {p : Mate G} (A : Square p) (q : Mate G) where
  count : ℕ
  choices : Fin count → Mate G
  exact_loss : A.lost q=2*count
  each_two : ∀ j,A.lost (choices j)=2
  cost_bound : (∑ j : Fin count, (cost M (choices j)-cost M p)) ≤ cost M q-cost M p

noncomputable def row [Fintype I] (M : Marking G I) {p : Mate G} (A : Square p)
    (min : ∀ r,cost M p≤cost M r)
    (unmarked : ∀ i t,M.a i≠A.corner t) (no : A.NoDiagonal)
    (q : Mate G) (D : Decomposition A q) : Row M A q := by
  classical
  cases D with
  | none h =>
    exact ⟨0,Fin.elim0,by simpa using A.lost_none h,(fun j=>j.elim0),by simp⟩
  | two i j ne h S =>
    have matchIJ := A.q_pairs_two h
    have e : G.Adj (A.corner i) (A.corner j) := by
      rw [←matchIJ]
      exact q.edge _
    have close : Closed q S.strip.support := by
      intro x m
      rcases m with r|rfl|rfl
      · exact Or.inl (S.strip.q_internal x r)
      · exact Or.inr (Or.inr matchIJ)
      · exact Or.inr (Or.inl (Mate.reverse matchIJ))
    refine ⟨1,fun _=>S.strip.release e,by simpa using A.lost_two ne h,
      fun _=>A.lost_two ne (A.release_opens S e),?_⟩
    have bound := one_cost_bound M p q S.strip e close (fun l=>unmarked l i) (fun l=>unmarked l j) min
    simp
    omega
  | four i j k l distinct h S T apart =>
    obtain ⟨adj1,adj2⟩ := A.nondiagonal_pairs distinct S T apart no
    let e₁ := A.edges i j adj1
    let e₂ := A.edges k l adj2
    have allCorners (t : Fin 4) : A.corner t∈S.strip.support∪T.strip.support := by
      rcases Square.four_cover i j k l distinct t with rfl|rfl|rfl|rfl
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inl (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    have cornerClosed (t : Fin 4) : q.mate (A.corner t)∈S.strip.support∪T.strip.support := by
      rcases A.only t _ (q.edge _) with p|⟨a,_,r⟩
      · exact (h t p).elim
      · exact r.symm ▸ allCorners a
    have close : Closed q (S.strip.support∪T.strip.support) := by
      intro x m
      rcases m with ⟨inS|rfl|rfl⟩|⟨inT|rfl|rfl⟩
      · exact Or.inl (Or.inl (S.strip.q_internal x inS))
      · exact cornerClosed i
      · exact cornerClosed j
      · exact Or.inr (Or.inl (T.strip.q_internal x inT))
      · exact cornerClosed k
      · exact cornerClosed l
    let moves (a : Fin 2) := if a=0 then S.strip.release e₁ else T.strip.release e₂
    refine ⟨2,moves,by simpa using A.lost_four h,?_ ,?_⟩
    · intro a
      by_cases zero : a=0
      · simpa [moves,zero] using A.lost_two distinct.ij (A.release_opens S e₁)
      · simpa [moves,zero] using A.lost_two distinct.kl (A.release_opens T e₂)
    · have hb := two_cost_bound M p q S.strip T.strip e₁ e₂ apart close
        (fun x=>unmarked x i) (fun x=>unmarked x j)
        (fun x=>unmarked x k) (fun x=>unmarked x l) min
      rw [show (Finset.univ : Finset (Fin 2)) = {0,1} by decide,
        Finset.sum_insert (by decide),Finset.sum_singleton]
      simpa [moves] using hb

/-- Conditional formal cheap-pair theorem. The finite list of target
matchings comes with the specified two Edmonds-style expectations and
an exterior strip decomposition for each row. No diagonal exterior
linkage and no marked corner then force a budget-feasible two-edge release. -/
theorem affordable_unmarked_square [Fintype I] {ι : Type*} [Fintype ι]
    (M : Marking G I) (p : Mate G) (A : Square p)
    (min : ∀ r,cost M p≤cost M r) (atMostOne : cost M p≤1)
    (unmarked : ∀ i t,M.a i≠A.corner t) (no : A.NoDiagonal)
    (targets : ι→Mate G) (split : ∀ i,Decomposition A (targets i))
    (weight : ι→ℚ) (nonneg : ∀ i,0≤weight i)
    (meanGain : (∑ i : ι,weight i*((cost M (targets i)-cost M p : ℕ) : ℚ))=
      ((2-cost M p : ℕ) : ℚ))
    (meanLost : (∑ i : ι,weight i*(A.lost (targets i) : ℚ))=(8:ℚ)/3) :
    ∃ q : Mate G,A.lost q=2 ∧ cost M q≤1 := by
  classical
  let rows (i : ι) := row M A min unmarked no (targets i) (split i)
  have pos : 0 < 2-cost M p := by omega
  obtain ⟨i,j,small⟩ := RemoteBudgetExpectation.four_edge_affordable
    weight nonneg (2-cost M p) pos (fun i=>(rows i).count)
    (fun i j=>cost M ((rows i).choices j) - cost M p)
    (fun i=>cost M (targets i) - cost M p) (fun i=>A.lost (targets i))
    (fun i=>(rows i).exact_loss) (fun i=>(rows i).cost_bound)
    meanGain meanLost
  have lower := min ((rows i).choices j)
  exact ⟨(rows i).choices j,(rows i).each_two j,by omega⟩

#print axioms Square.nondiagonal_pairs
#print axioms row
#print axioms affordable_unmarked_square
end KelmansCactus.AtomicBridge.RemoteSquareBudgetConditional
