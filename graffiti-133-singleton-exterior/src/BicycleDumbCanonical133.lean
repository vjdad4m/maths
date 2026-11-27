import BicycleDumbPath133
import BicycleTripleLayout133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133Revisit
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}

theorem Relay.loop_size_lower {B : Finset V} {w : V} (P : Relay G B w w) (wB : w∈B)
    (two : 2≤P.n)
    (tri : ∀ a b c,G.Adj a b→G.Adj b c→G.Adj c a→False)
    (h4 : FourCycleFree G) : 4≤P.n := by
  rcases (show P.n=2 ∨ P.n=3 ∨ 4≤P.n by omega) with h|h|h
  · let i : Fin P.n := ⟨0,by omega⟩
    let j : Fin P.n := ⟨1,by omega⟩
    have a := (P.attached i w wB).mpr (Or.inl ⟨rfl,rfl⟩)
    have b := (P.path.2 i j (by change (0:Nat)<1; decide)).mpr rfl
    have c := (P.attached j w wB).mpr (Or.inr ⟨by change 1+1=P.n; omega,rfl⟩)
    exact (tri _ _ _ a b c.symm).elim
  · let i : Fin P.n := ⟨0,by omega⟩
    let j : Fin P.n := ⟨1,by omega⟩
    let k : Fin P.n := ⟨2,by omega⟩
    have a := (P.attached i w wB).mpr (Or.inl ⟨rfl,rfl⟩)
    have b := ((P.path.2 i j (by change (0:Nat)<1; decide)).mpr rfl).symm
    have c := (P.attached k w wB).mpr (Or.inr ⟨by change 2+1=P.n; omega,rfl⟩)
    have d := (P.path.2 j k (by change (1:Nat)<2; decide)).mpr rfl
    have ne : w≠P.f j := fun e=>P.off j (e ▸ wB)
    have e := congrArg Fin.val (P.path.1 (h4 _ _ _ _ ne a b c d))
    change 0=2 at e
    omega
  · exact h

private theorem DumbRelays.numbered_model_transfer (P : DumbRelays G u v) (uv : u≠v)
    {sz : Fin 3 → Nat} (eq : P.network.sizes=sz) {m : Nat} (labels : Fin m→RouteIndex sz)
    (li : Function.Injective labels) (R : Nat → Nat → Prop)
    (matchAdj : ∀ i j, routeAdj sz dumbStart dumbEnd (sz 1=0) (labels i) (labels j) ↔ R i.val j.val) :
    ∃ f : Fin m → V, Function.Injective f ∧
      ∀ i j,G.Adj (f i) (f j) ↔ R i.val j.val := by
  subst sz
  have eqMid : P.network.sizes 1=P.mid.n := rfl
  refine ⟨P.network.vertex ∘ labels,(P.network.vertex_injective uv).comp li,?_⟩
  intro i j
  have v := P.network.vertex_adj uv (labels i) (labels j)
  change G.Adj _ _ ↔ routeAdj P.network.sizes dumbStart dumbEnd (P.mid.n=0) (labels i) (labels j) at v
  rw [←eqMid] at v
  exact v.trans (matchAdj i j)

theorem DumbRelays.canonical_dumb (P : DumbRelays G u v) (uv : u≠v)
    (tri : ∀ a b c,G.Adj a b→G.Adj b c→G.Adj c a→False)
    (h4 : FourCycleFree G) (no9 : ¬∃ p : Fin 9 → V, InducedPath G p) :
    ∃ f : Fin 10 → V, Function.Injective f ∧
      ∀ i j,G.Adj (f i) (f j) ↔ dumbRelation 5 5 1 i.val j.val=true := by
  have left := P.first.loop_size_lower (by simp) P.longFirst tri h4
  have right := P.last.loop_size_lower (by simp) P.longLast tri h4
  have hi : P.first.n+P.mid.n+P.last.n≤8 := by
    by_cases small : P.first.n+P.mid.n+P.last.n≤8
    · exact small
    exfalso
    obtain ⟨p,hp⟩ := P.long_path uv
    exact no9 (trim_path (by omega) hp)
  have a : P.first.n=4 := by omega
  have b : P.mid.n=0 := by omega
  have c : P.last.n=4 := by omega
  have sd : P.network.sizes=sizeVec 4 0 4 := by
    funext i
    fin_cases i
    · exact a
    · exact b
    · exact c
  exact P.numbered_model_transfer uv sd numberedDumb551 (fun i j e=>dumbLayout551.1 i j e)
    (fun i j=>dumbRelation 5 5 1 i j=true) dumbLayout551.2

#print axioms DumbRelays.canonical_dumb
end Graffiti133Bicycle
