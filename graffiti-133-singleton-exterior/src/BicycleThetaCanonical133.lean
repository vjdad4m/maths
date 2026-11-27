import BicycleThetaUpper133
import BicycleThetaLower133
import BicycleTripleLayout133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}

private theorem sorted_three (d : Fin 3 → Nat) :
    ∃ e : Fin 3 ≃ Fin 3, d (e 0)≤d (e 1) ∧ d (e 1)≤d (e 2) := by
  let E01 := Equiv.swap (0:Fin 3) 1
  let E02 := Equiv.swap (0:Fin 3) 2
  let E12 := Equiv.swap (1:Fin 3) 2
  by_cases a : d 0≤d 1
  · by_cases b : d 1≤d 2
    · exact ⟨Equiv.refl _,a,b⟩
    · by_cases c : d 0≤d 2
      · exact ⟨E12,c,by change d 2≤d 1; omega⟩
      · exact ⟨E02.trans E01,by change d 2≤d 0; omega,by change d 0≤d 1; exact a⟩
  · by_cases c : d 0≤d 2
    · exact ⟨E01,by change d 1≤d 0; omega,c⟩
    · by_cases b : d 1≤d 2
      · exact ⟨E01.trans E02,b,by change d 2≤d 0; omega⟩
      · exact ⟨E02,by change d 2≤d 1; omega,by change d 1≤d 0; omega⟩

def ThetaRelays.reorder (P : ThetaRelays G u v) (e : Fin 3 ≃ Fin 3) : ThetaRelays G u v where
  rel := P.rel ∘ e
  sep := fun i j h => P.sep _ _ (e.injective.ne h)
  direct := P.direct.trans ⟨fun ⟨i,h⟩=>⟨e.symm i,by simpa using h⟩,fun ⟨i,h⟩=>⟨e i,h⟩⟩
  atMostOneEmpty := fun i j hi hj => e.injective (P.atMostOneEmpty _ _ hi hj)

private theorem ThetaRelays.numbered_model_transfer (P : ThetaRelays G u v) (uv : u≠v)
    {sz : Fin 3 → Nat} (szEq : P.network.sizes=sz) {m : Nat} (f : Fin m → RouteIndex sz)
    (fi : Function.Injective f) (R : Nat → Nat → Prop)
    (s : ∀ i j, routeAdj sz (fun _=>false) (fun _=>true) (∃ k,sz k=0) (f i) (f j) ↔ R i.val j.val) :
    ∃ q : Fin m → V, Function.Injective q ∧
      ∀ i j,G.Adj (q i) (q j) ↔ R i.val j.val := by
  subst sz
  exact ⟨P.network.vertex ∘ f,(P.network.vertex_injective uv).comp fi,
    fun i j => (P.network.vertex_adj uv (f i) (f j)).trans (s i j)⟩

theorem ThetaRelays.canonical_theta (P : ThetaRelays G u v) (uv : u≠v)
    (tri : ∀ a b c,G.Adj a b→G.Adj b c→G.Adj c a→False) (h4 : FourCycleFree G)
    (no9 : ¬∃ p : Fin 9 → V, InducedPath G p) :
    ∃ a b c, (a,b,c)∈thetaKeys ∧
      ∃ f : Fin (2+(a-1)+(b-1)+(c-1)) → V, Function.Injective f ∧
        ∀ i j,G.Adj (f i) (f j) ↔ thetaRelation a b c i.val j.val=true := by
  obtain ⟨e,ab,bc⟩ := sorted_three fun i => (P.rel i).n
  let Q := P.reorder e
  let a := (Q.rel 0).n+1
  let b := (Q.rel 1).n+1
  let c := (Q.rel 2).n+1
  change (Q.rel 0).n≤(Q.rel 1).n at ab
  change (Q.rel 1).n≤(Q.rel 2).n at bc
  have lo := Q.pair_size_lower uv tri h4 0 1 (by decide)
  have hi := Q.pair_size_upper uv no9 1 2 (by decide)
  have keys := theta_keys_complete a b c (by dsimp [a]; omega)
    (by dsimp [a,b]; omega) (by dsimp [b,c]; omega)
    (by dsimp [a,b]; omega) (by dsimp [b,c]; omega)
  refine ⟨a,b,c,keys,?_⟩
  have eq : Q.network.sizes=sizeVec (a-1) (b-1) (c-1) := by
    funext i
    fin_cases i <;> simp [ThetaRelays.network, TripleNetwork.sizes, sizeVec,a,b,c]
  have cond := thetaLayout_of_key a b c keys
  exact Q.numbered_model_transfer uv eq
    (numberedRoute (a-1) (b-1) (c-1)) (fun i j h=>cond.1 i j h)
    (fun i j=>thetaRelation a b c i j=true) cond.2

#print axioms ThetaRelays.canonical_theta
end Graffiti133Bicycle
