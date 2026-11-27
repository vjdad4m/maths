import BicycleRelayNetworks133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Finset
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}

def hub (u v : V) (b : Bool) : V := if b then v else u

theorem hub_injective (uv : u≠v) : Function.Injective (hub u v) := by
  intro a b h
  cases a <;> cases b <;> simp_all [hub]

theorem hub_mem (u v : V) (b : Bool) : hub u v b∈({u,v} : Finset V) := by
  cases b <;> simp [hub]

structure TripleNetwork (G : SimpleGraph V) (u v : V) where
  heads : Fin 3 → Bool
  tails : Fin 3 → Bool
  delta : Prop
  rel : (i : Fin 3) → Relay G {u,v} (hub u v (heads i)) (hub u v (tails i))
  sep : ∀ i j, i≠j → (rel i).Separated (rel j)
  direct : G.Adj u v ↔ delta

def ThetaRelays.network (P : ThetaRelays G u v) : TripleNetwork G u v where
  heads := fun _=>false
  tails := fun _=>true
  delta := ∃ i,(P.rel i).n=0
  rel := P.rel
  sep := P.sep
  direct := P.direct

def dumbStart (k : Fin 3) : Bool := decide (k.val=2)
def dumbEnd (k : Fin 3) : Bool := decide (k.val≠0)

def DumbRelays.network (P : DumbRelays G u v) : TripleNetwork G u v := by
  let C (i : Fin 3) : Relay G ({u,v} : Finset V) (hub u v (dumbStart i)) (hub u v (dumbEnd i)) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact P.first
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact P.mid
      · have e : k=0 := Subsingleton.elim _ _
        subst k
        exact P.last
  refine ⟨dumbStart,dumbEnd,P.mid.n=0,C,?_,P.direct⟩
  intro i j ne
  fin_cases i <;> fin_cases j
  all_goals first | contradiction | exact P.f_m | exact P.f_l | exact P.m_l | exact P.f_m.symm | exact P.f_l.symm | exact P.m_l.symm

def TripleNetwork.sizes (P : TripleNetwork G u v) (k : Fin 3) := (P.rel k).n

abbrev RouteIndex (sz : Fin 3 → Nat) := Sum Bool (Σ k : Fin 3, Fin (sz k))

def routeAdj (sz : Fin 3 → Nat) (hd tl : Fin 3 → Bool) (delta : Prop) :
    RouteIndex sz → RouteIndex sz → Prop
  | .inl h, .inl j => h≠j ∧ delta
  | .inl h, .inr ⟨k,i⟩ | .inr ⟨k,i⟩, .inl h =>
    (i.val=0 ∧ h=hd k) ∨ (i.val+1=sz k ∧ h=tl k)
  | .inr ⟨k,i⟩, .inr ⟨l,j⟩ => k=l ∧ (i.val+1=j.val ∨ j.val+1=i.val)

instance (sz : Fin 3 → Nat) (hd tl : Fin 3 → Bool) (delta : Prop) [Decidable delta]
    (a b : RouteIndex sz) : Decidable (routeAdj sz hd tl delta a b) := by
  cases a <;> cases b <;> unfold routeAdj
  all_goals infer_instance

def TripleNetwork.vertex (P : TripleNetwork G u v) : RouteIndex P.sizes → V
  | .inl h => hub u v h
  | .inr ⟨i,k⟩ => (P.rel i).f k

theorem TripleNetwork.vertex_injective (P : TripleNetwork G u v) (uv : u≠v) :
    Function.Injective P.vertex := by
  rintro (a|⟨k,i⟩) (b|⟨l,j⟩) e
  · exact congrArg Sum.inl (hub_injective uv e)
  · change hub u v a=(P.rel l).f j at e
    exact ((P.rel l).off j (e ▸ hub_mem u v a)).elim
  · change (P.rel k).f i=hub u v b at e
    exact ((P.rel k).off i (e.symm ▸ hub_mem u v b)).elim
  · by_cases kl : k=l
    · subst l
      exact congrArg (fun q : Fin (P.sizes k) => (Sum.inr ⟨k,q⟩ : RouteIndex P.sizes)) ((P.rel k).path.1 e)
    · exact ((P.sep k l kl i j).1 e).elim

theorem TripleNetwork.vertex_adj (P : TripleNetwork G u v) (uv : u≠v) (i j : RouteIndex P.sizes) :
    G.Adj (P.vertex i) (P.vertex j) ↔ routeAdj P.sizes P.heads P.tails P.delta i j := by
  rcases i with a|⟨k,i⟩ <;> rcases j with b|⟨l,j⟩
  · cases a <;> cases b <;> simp [TripleNetwork.vertex,hub,routeAdj,P.direct,G.adj_comm v u]
  · change G.Adj (hub u v a) ((P.rel l).f j) ↔
      ((j.val=0 ∧ a=P.heads l) ∨ (j.val+1=P.sizes l ∧ a=P.tails l))
    rw [(P.rel l).attached j _ (hub_mem u v a)]
    simp only [(hub_injective uv).eq_iff,TripleNetwork.sizes]
  · rw [G.adj_comm]
    change G.Adj (hub u v b) ((P.rel k).f i) ↔
      ((i.val=0 ∧ b=P.heads k) ∨ (i.val+1=P.sizes k ∧ b=P.tails k))
    rw [(P.rel k).attached i _ (hub_mem u v b)]
    simp only [(hub_injective uv).eq_iff,TripleNetwork.sizes]
  · by_cases kl : k=l
    · subst l
      simpa [TripleNetwork.vertex, routeAdj] using induced_adj_both_orders (P.rel k).path i j
    · simp only [routeAdj,kl,false_and]
      exact ⟨(P.sep k l kl i j).2,False.elim⟩

#print axioms TripleNetwork.vertex_adj
end Graffiti133Bicycle
