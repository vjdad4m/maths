import RemoteSquareConvergence

namespace KelmansCactus.AtomicBridge.RemoteRankUnion
open SimpleGraph
open RemoteSquareConvergence (pair lift_reach)
variable {V P S : Type*}

structure Marking (G : SimpleGraph V) (P : Type*) where
  a : P→V
  b : P→V
  edge : ∀ p,G.Adj (a p) (b p)

def Marking.marked {G : SimpleGraph V} (M : Marking G P) (x y : V) : Prop :=
  ∃ p,pair (M.a p) (M.b p) x y

theorem Marking.marked_symm {G : SimpleGraph V} (M : Marking G P) {x y : V} :
    M.marked x y → M.marked y x := by
  rintro ⟨p,h⟩
  rcases h with ⟨l,r⟩|⟨l,r⟩
  · exact ⟨p,Or.inr ⟨r,l⟩⟩
  · exact ⟨p,Or.inl ⟨r,l⟩⟩

structure MatchingFamily (G : SimpleGraph V) (S : Type*) where
  mate : S→V→V
  involutive : ∀ s,Function.Involutive (mate s)
  adjacent : ∀ s x,G.Adj x (mate s x)

theorem MatchingFamily.symm_eq {G : SimpleGraph V} (Q : MatchingFamily G S)
    {x y : V} {s : S} (e : Q.mate s x=y) : Q.mate s y=x := by
  rw [← e,Q.involutive]

theorem MatchingFamily.symm_neq {G : SimpleGraph V} (Q : MatchingFamily G S)
    {x y : V} {s : S} (e : Q.mate s x≠y) : Q.mate s y≠x :=
  fun h=>e (Q.symm_eq h)

/-- Union of all complementary ranks, with every subdivided mark contracted
to its original edge even if it is omitted by a particular rank. -/
def union {G : SimpleGraph V} (M : Marking G P) (Q : MatchingFamily G S) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∧ (M.marked x y ∨ ∃ s,Q.mate s x≠y)
  symm := by
    rintro x y ⟨e,h|⟨s,h⟩⟩
    · exact ⟨e.symm,Or.inl (M.marked_symm h)⟩
    · exact ⟨e.symm,Or.inr ⟨s,Q.symm_neq h⟩⟩
  loopless := fun x h=>G.loopless x h.1

def rebuiltUnion {G : SimpleGraph V} (M : Marking G P) (Q : MatchingFamily G S) :
    SimpleGraph (V⊕P) where
  Adj
  | .inl x,.inl y => G.Adj x y ∧ ¬M.marked x y ∧ ∃ s,Q.mate s x≠y
  | .inl x,.inr p => x=M.a p ∨ x=M.b p
  | .inr p,.inl x => x=M.a p ∨ x=M.b p
  | .inr _,.inr _ => False
  symm := by
    rintro (x|p) (y|q) h
    · obtain ⟨e,no,s,ne⟩ := h
      exact ⟨e.symm,fun w=>no (M.marked_symm w),s,Q.symm_neq ne⟩
    all_goals exact h
  loopless := by
    rintro (x|p) h
    · exact G.loopless x h.1
    · exact h

def contract {G : SimpleGraph V} (M : Marking G P) : V⊕P→V
  | .inl x => x
  | .inr p => M.a p

theorem reachable_image {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (f : A→B) (step : ∀ x y,G.Adj x y → H.Reachable (f x) (f y))
    {x y : A} (r : G.Reachable x y) : H.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := r
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h _ ih => exact (step _ _ h).trans ih

theorem contraction_reaches {G : SimpleGraph V} (M : Marking G P) (Q : MatchingFamily G S)
    {x y : V⊕P} :
    (rebuiltUnion M Q).Reachable x y →
    (union M Q).Reachable (contract M x) (contract M y) := by
  apply reachable_image (contract M)
  rintro (x|p) (y|q) e
  · exact SimpleGraph.Adj.reachable (G:=union M Q) ⟨e.1,Or.inr e.2.2⟩
  · rcases e with rfl|rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (G:=union M Q)
        ⟨(M.edge q).symm,Or.inl ⟨q,Or.inr ⟨rfl,rfl⟩⟩⟩
  · rcases e with rfl|rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (G:=union M Q)
        ⟨M.edge p,Or.inl ⟨p,Or.inl ⟨rfl,rfl⟩⟩⟩
  · exact e.elim

theorem expansion_reaches {G : SimpleGraph V} (M : Marking G P) (Q : MatchingFamily G S)
    {x y : V} :
    (union M Q).Reachable x y →
      (rebuiltUnion M Q).Reachable (.inl x) (.inl y) := by
  classical
  apply reachable_image Sum.inl
  rintro u v ⟨edge,pos⟩
  by_cases m : M.marked u v
  · obtain ⟨p,h⟩ := m
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (SimpleGraph.Adj.reachable (G:=rebuiltUnion M Q)
         (u:=.inl (M.a p)) (v:=.inr p) (Or.inl rfl)).trans
        (SimpleGraph.Adj.reachable (G:=rebuiltUnion M Q)
         (u:=.inr p) (v:=.inl (M.b p)) (Or.inr rfl))
    · exact (SimpleGraph.Adj.reachable (G:=rebuiltUnion M Q)
         (u:=.inl (M.b p)) (v:=.inr p) (Or.inr rfl)).trans
        (SimpleGraph.Adj.reachable (G:=rebuiltUnion M Q)
         (u:=.inr p) (v:=.inl (M.a p)) (Or.inl rfl))
  · exact SimpleGraph.Adj.reachable (G:=rebuiltUnion M Q)
      ⟨edge,m,pos.elim (fun h=>(m h).elim) id⟩

theorem rebuilt_preconnected_iff {G : SimpleGraph V} (M : Marking G P)
    (Q : MatchingFamily G S) :
    (rebuiltUnion M Q).Preconnected ↔ (union M Q).Preconnected := by
  constructor
  · intro h x y
    exact contraction_reaches M Q (h (.inl x) (.inl y))
  · intro h x y
    have atOld (v : V⊕P) : (rebuiltUnion M Q).Reachable v (.inl (contract M v)) := by
      rcases v with (v|p)
      · exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (G:=rebuiltUnion M Q) (Or.inl rfl)
    exact (atOld x).trans ((expansion_reaches M Q (h _ _)).trans (atOld y).symm)

def ForcedCut {G : SimpleGraph V} (M : Marking G P) (Q : MatchingFamily G S)
    (c : V→Bool) : Prop :=
  ∀ x y,G.Adj x y → c x≠c y → ¬M.marked x y ∧ ∀ s,Q.mate s x=y

/-- The genuine fixed-state union is disconnected only through cuts of
unmarked edges forced in every admissible complementary matching.
Conversely every nonconstant such cut is an obstruction. -/
theorem rebuilt_disconnected_iff_forced_cut {G : SimpleGraph V} (M : Marking G P)
    (Q : MatchingFamily G S) :
    ¬(rebuiltUnion M Q).Preconnected ↔
      ∃ c : V→Bool,(∃ x y,c x≠c y) ∧ ForcedCut M Q c := by
  classical
  rw [rebuilt_preconnected_iff M Q]
  constructor
  · intro h
    change ¬∀ x y,(union M Q).Reachable x y at h
    push_neg at h
    rcases h with ⟨x,y,xy⟩
    let c (z : V) := decide ((union M Q).Reachable x z)
    refine ⟨c,⟨x,y,?_⟩,?_⟩
    · simp [c,xy,SimpleGraph.Reachable.refl]
    intro u v edge crossing
    have no : ¬(union M Q).Adj u v := by
      intro e
      apply crossing
      have iff : (union M Q).Reachable x u ↔ (union M Q).Reachable x v :=
        ⟨fun p=>p.trans e.reachable,fun p=>p.trans e.symm.reachable⟩
      simp [c,iff]
    constructor
    · exact fun m=>no ⟨edge,Or.inl m⟩
    · intro s
      by_contra hm
      exact no ⟨edge,Or.inr ⟨s,hm⟩⟩
  · rintro ⟨c,⟨x,y,bad⟩,force⟩ hc
    have path := hc x y
    rw [SimpleGraph.reachable_iff_reflTransGen] at path
    have const : ∀ v, Relation.ReflTransGen (union M Q).Adj x v → c x=c v := by
      intro v proof
      induction proof with
      | refl => rfl
      | tail _ e ih =>
        apply ih.trans
        by_contra no
        rcases force _ _ e.1 no with ⟨unmarked,always⟩
        exact e.2.elim unmarked (fun ⟨s,hs⟩=>hs (always s))
    exact bad (const _ path)

/-- Each original forced cut is a matching, hence a nontrivial cyclic-four
cut can have no shore of size one if the original graph has min degree 2. -/
theorem force_cut_has_distinct_same_color {G : SimpleGraph V} (M : Marking G P)
    (Q : MatchingFamily G S) (s : S)
    (c : V→Bool) (cut : ForcedCut M Q c)
    (two : ∀ x,∃ y z,G.Adj x y ∧ G.Adj x z ∧ y≠z) :
    ∀ x,∃ y,y≠x ∧ c y=c x := by
  intro x
  obtain ⟨y,z,xy,xz,n⟩ := two x
  by_cases same : c x=c y
  · exact ⟨y,(G.ne_of_adj xy).symm,same.symm⟩
  have zSame : c x=c z := by
    by_contra nz
    exact n (((cut x y xy same).2 s).symm.trans ((cut x z xz nz).2 s))
  exact ⟨z,(G.ne_of_adj xz).symm,zSame.symm⟩

#print axioms rebuilt_preconnected_iff
#print axioms rebuilt_disconnected_iff_forced_cut
#print axioms force_cut_has_distinct_same_color
end KelmansCactus.AtomicBridge.RemoteRankUnion
