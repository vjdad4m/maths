import DiagonalReleaseFixture

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge.DiagonalPairUnion
open DiagonalReleaseFixture (Core Board core board q q_inv decode route)
open SquareCap (IsTile HasFactor)

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



abbrev ranked (t : Fin 3) := rankOf (q t) (q_inv t)
abbrev rank0 := rebuilt (ranked 0)
abbrev rank1 := rebuilt (ranked 1)

/-- This is the union of these two specific ranks, not all budget-feasible ranks. -/
def pairUnion : SimpleGraph Board := rank0 ⊔ rank1
instance : DecidableRel pairUnion.Adj := by
  intro x y
  change Decidable (rank0.Adj x y ∨ rank1.Adj x y)
  infer_instance

theorem pairwise_exact (x y : Board) : pairUnion.Adj x y ↔ rank0.Adj x y ∨ rank1.Adj x y :=
  Iff.rfl

def isolation0 : Finset Board := (route [0,1,2,3]).toFinset
def isolation1 : Finset Board := (route [0,3,9,23,8,1,2,5,22,4]).toFinset

set_option maxRecDepth 8000 in
theorem isolation0_geometry : isolation0.card=4 ∧ Closed rank0 isolation0 := by decide
set_option maxRecDepth 8000 in
theorem isolation1_geometry : isolation1.card=10 ∧ Closed rank1 isolation1 := by decide

theorem rank0_no_factor : ¬HasFactor rank0 := by
  apply no_factor_closed_mod _ isolation0_geometry.2
  rw [isolation0_geometry.1]
  decide

theorem rank1_no_factor : ¬HasFactor rank1 := by
  apply no_factor_closed_mod _ isolation1_geometry.2
  rw [isolation1_geometry.1]
  decide

def spanning : List Board := route [6,18,13,14,19,7,4,22,5,2,1,0,3,9,10,20,16,15,12,17,21,11,8,23]
theorem spanning_geometry :
    spanning.Nodup ∧ spanning.length=24 ∧ spanning.toFinset=univ ∧
    spanning.Chain' pairUnion.Adj := by decide
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


theorem pair_connected : pairUnion.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable pairUnion).mpr
  refine ⟨decode 6,?_⟩
  intro x
  apply reach_of_route (route [18,13,14,19,7,4,22,5,2,1,0,3,9,10,20,16,15,12,17,21,11,8,23])
  · exact spanning_geometry.2.2.2
  · have h : x∈spanning.toFinset := by rw [spanning_geometry.2.2.1]; exact mem_univ _
    exact List.mem_toFinset.mp h

private def triple (u v w : Nat) : Finset Board := {decode u,decode v,decode w}
private def tiles : Finset (Finset Board) :=
  {triple 12 15 16,triple 11 21 17,triple 9 10 20,triple 1 8 23,
   triple 3 0 4,triple 2 5 22,triple 7 6 18,triple 13 14 19}

theorem pair_factor : HasFactor pairUnion := by
  refine ⟨tiles,?_,?_,?_⟩
  · change ∀ A ∈ tiles,A.card=3 ∧ ∃ c∈A,∀ x∈A,x≠c → pairUnion.Adj c x
    decide
  · decide
  · decide

#print axioms pairwise_exact
#print axioms rank0_no_factor
#print axioms rank1_no_factor
#print axioms pair_connected
#print axioms pair_factor
end KelmansCactus.AtomicBridge.DiagonalPairUnion
