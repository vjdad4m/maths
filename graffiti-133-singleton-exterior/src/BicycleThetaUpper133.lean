import BicycleTripleNetwork133
import LocalDensity133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133Revisit
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}

private def routeIndexValue {sz : Fin 3 → Nat} (a : RouteIndex sz) : Nat :=
  match a with | .inl _ => 0 | .inr s => s.2.val

private def routeIndexTag {sz : Fin 3 → Nat} (a : RouteIndex sz) : Option (Fin 3) :=
  match a with | .inl _ => none | .inr s => some s.1

theorem ThetaRelays.two_relay_path (P : ThetaRelays G u v) (uv : u≠v)
    (k l : Fin 3) (ne : k≠l) :
    ∃ f : Fin ((P.rel k).n+(P.rel l).n+1) → V, InducedPath G f := by
  let N := P.network
  let sz := N.sizes
  let a := sz k
  let b := sz l
  let Q (i : Fin (a+b+1)) : RouteIndex sz :=
    if h : i.val<a then .inr ⟨k,⟨a-1-i.val,by omega⟩⟩
      else if h : i.val=a then .inl false else .inr ⟨l,⟨i.val-(a+1),by omega⟩⟩
  have lf (i : Fin (a+b+1)) (hi : i.val<a) :
      Q i = .inr ⟨k,⟨a-1-i.val,by omega⟩⟩ := dif_pos hi
  have md (i : Fin (a+b+1)) (hi : i.val=a) : Q i = .inl false := by
    unfold Q
    rw [dif_neg (by omega),dif_pos hi]
  have rt (i : Fin (a+b+1)) (hi : a < i.val) :
      Q i = .inr ⟨l,⟨i.val-(a+1),by omega⟩⟩ := by
    unfold Q
    rw [dif_neg (by omega),dif_neg (by omega)]
  have injQ : Function.Injective Q := by
    intro i j e
    have valEq := congrArg routeIndexValue e
    have tagEq := congrArg routeIndexTag e
    rcases lt_trichotomy i.val a with il|im|ir <;> rcases lt_trichotomy j.val a with jl|jm|jr
    · rw [lf i il,lf j jl] at valEq
      change a-1-i.val=a-1-j.val at valEq
      exact Fin.ext (by omega)
    · rw [lf i il,md j jm] at tagEq
      contradiction
    · rw [lf i il,rt j jr] at tagEq
      exact (ne (Option.some.inj tagEq)).elim
    · rw [md i im,lf j jl] at tagEq
      contradiction
    · exact Fin.ext (im.trans jm.symm)
    · rw [md i im,rt j jr] at tagEq
      contradiction
    · rw [rt i ir,lf j jl] at tagEq
      exact (ne (Option.some.inj tagEq).symm).elim
    · rw [rt i ir,md j jm] at tagEq
      contradiction
    · rw [rt i ir,rt j jr] at valEq
      change i.val-(a+1)=j.val-(a+1) at valEq
      exact Fin.ext (by omega)
  refine ⟨N.vertex ∘ Q,(N.vertex_injective uv).comp injQ,?_⟩
  intro i j lij
  change G.Adj (N.vertex (Q i)) (N.vertex (Q j)) ↔ _
  rw [N.vertex_adj uv]
  have lij' : i.val < j.val := lij
  rcases lt_trichotomy i.val a with il|im|ir
  · rcases lt_trichotomy j.val a with jl|jm|jr
    · rw [lf i il,lf j jl]
      change k=k ∧ ((a-1-i.val)+1=a-1-j.val ∨ (a-1-j.val)+1=a-1-i.val) ↔ _
      simp only [eq_self_iff_true,true_and]
      omega
    · rw [lf i il,md j jm]
      change ((a-1-i.val=0 ∧ false=false) ∨ ((a-1-i.val)+1=a ∧ false=true)) ↔ _
      simp only [and_true, Bool.false_eq_true,and_false,or_false]
      omega
    · rw [lf i il,rt j jr]
      simp only [routeAdj,ne,false_and,false_iff]
      omega
  · have jr : a < j.val := by omega
    rw [md i im,rt j jr]
    change ((j.val-(a+1)=0 ∧ false=false) ∨ (j.val-(a+1)+1=b ∧ false=true)) ↔ _
    simp only [and_true,Bool.false_eq_true,and_false,or_false]
    omega
  · have jr : a < j.val := by omega
    rw [rt i ir,rt j jr]
    change l=l ∧ ((i.val-(a+1))+1=j.val-(a+1) ∨ (j.val-(a+1))+1=i.val-(a+1)) ↔ _
    simp only [eq_self_iff_true,true_and]
    omega

theorem ThetaRelays.pair_size_upper (P : ThetaRelays G u v) (uv : u≠v)
    (no9 : ¬∃ f : Fin 9 → V, InducedPath G f) (k l : Fin 3) (ne : k≠l) :
    (P.rel k).n+(P.rel l).n≤7 := by
  by_cases b : (P.rel k).n+(P.rel l).n ≤ 7
  · exact b
  exfalso
  obtain ⟨f,hf⟩ := P.two_relay_path uv k l ne
  exact no9 (trim_path (by omega) hf)

#print axioms ThetaRelays.two_relay_path
#print axioms ThetaRelays.pair_size_upper
end Graffiti133Bicycle
