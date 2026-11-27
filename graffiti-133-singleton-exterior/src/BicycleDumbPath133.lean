import BicycleRelayNetworks133
import BicycleConcat133
import LocalDensity133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133Camby Graffiti133Revisit
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}

theorem DumbRelays.long_path (P : DumbRelays G u v) (uv : u≠v) :
    ∃ f : Fin (P.first.n+P.mid.n+P.last.n)→V, InducedPath G f := by
  classical
  let a := P.first.n-1
  let b := P.mid.n
  let c := P.last.n-1
  have pa : 2≤P.first.n := P.longFirst
  have pc : 2≤P.last.n := P.longLast
  have ab : a+1=P.first.n := by dsimp [a]; omega
  have cb : c+1=P.last.n := by dsimp [c]; omega
  have aPos : 0<a := by dsimp [a]; omega
  have uB : u∈({u,v}:Finset V) := by simp
  have vB : v∈({u,v}:Finset V) := by simp
  let castA : Fin a → Fin P.first.n := Fin.castLE (by omega)
  let castC : Fin c → Fin P.last.n := Fin.castLE (by omega)
  let Lrev (i : Fin a) := P.first.f (castA (Fin.rev i))
  let L : Fin (a+1)→V := Fin.lastCases u Lrev
  let M : Fin (b+1)→V := Fin.lastCases v P.mid.f
  let R (j : Fin c) := P.last.f (castC j)
  have revval (i : Fin a) : (castA (Fin.rev i)).val=a-(i.val+1) := Fin.val_rev i
  have cval (i : Fin c) : (castC i).val=i.val := rfl
  have aVal (i : Fin a) : (castA i).val=i.val := rfl
  have pref : InducedPath G (P.first.f ∘ castA) := by
    refine ⟨P.first.path.1.comp (Fin.castLE_injective _),?_⟩
    intro i j lt
    exact P.first.path.2 (castA i) (castA j) lt
  have lrev : InducedPath G Lrev := reverse_path pref
  have nL : InducedPath G L := append_induced aPos lrev u
    (fun i h=>P.first.off (castA (Fin.rev i)) (Eq.mp (congrArg (fun x=>x∈({u,v}:Finset V)) h) uB))
    ((P.first.attached (castA (Fin.rev ⟨a-1,by omega⟩)) u uB).mpr (Or.inl
      ⟨by rw [revval]; change a-(a-1+1)=0; omega,rfl⟩))
    (fun i il h => by
      obtain e := (P.first.attached (castA (Fin.rev i)) u uB).mp h
      rw [revval] at e
      omega)
  have nM : InducedPath G M := by
    by_cases b0 : b=0
    · refine ⟨fun i j _ => Fin.ext (by have hi:=i.isLt; have hj:=j.isLt; omega),?_⟩
      intro i j lt
      have il : i.val < j.val := lt
      have jl := j.isLt
      omega
    · have pos : 0<b := by omega
      exact append_induced pos P.mid.path v
        (fun i h=>P.mid.off i (by simpa only [h] using vB))
        ((P.mid.attached ⟨b-1,by omega⟩ v vB).mpr (Or.inr
           ⟨by change b-1+1=b; omega,rfl⟩))
        (fun i hi e => by
          rcases (P.mid.attached i v vB).mp e with ⟨_,q⟩|⟨q,_⟩
          · exact uv q.symm
          · change i.val+1=b at q
            omega)
  have nR : InducedPath G R := by
    refine ⟨P.last.path.1.comp (Fin.castLE_injective _),?_⟩
    intro i j lt
    exact P.last.path.2 (castC i) (castC j) lt
  have Rfirst (j : Fin c) : G.Adj v (R j) ↔ j.val=0 := by
    change G.Adj v (P.last.f (castC j)) ↔ _
    rw [P.last.attached _ v vB,cval]
    simp only [and_true]
    have jl := j.isLt
    omega
  have Rnotu (j : Fin c) : ¬G.Adj u (R j) := by
    intro e
    rcases (P.last.attached (castC j) u uB).mp e with ⟨_,n⟩|⟨_,n⟩
    · exact uv n
    · exact uv n
  have aview (i : Fin (a+1)) :
      (i.val=a ∧ L i=u) ∨ ∃ k : Fin P.first.n, i.val<a ∧ L i=P.first.f k := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact Or.inl ⟨rfl,Fin.lastCases_last⟩
    · exact Or.inr ⟨castA (Fin.rev j),j.isLt,Fin.lastCases_castSucc _⟩
  have bview (i : Fin (b+1)) :
      (i.val=b ∧ M i=v) ∨ ∃ k : Fin b, i.val=k.val ∧ M i=P.mid.f k := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact Or.inl ⟨rfl,Fin.lastCases_last⟩
    · exact Or.inr ⟨j,rfl,Fin.lastCases_castSucc _⟩
  have LM (i : Fin (a+1)) (j : Fin (b+1)) :
      L i≠M j ∧ (G.Adj (L i) (M j) ↔ i.val+1=a+1 ∧ j.val=0) := by
    rcases aview i with ⟨ia,e⟩|⟨k,ia,e⟩ <;> rcases bview j with ⟨jb,q⟩|⟨l,jb,q⟩
    · rw [e,q,ia,jb,P.direct]
      simp [uv,b]
    · rw [e,q,ia,jb]
      have first : G.Adj u (P.mid.f l) ↔ l.val=0 := by
        rw [P.mid.attached _ u uB]
        simp [uv]
      exact ⟨fun h=>P.mid.off _ (by simpa only [h] using uB),by simpa using first⟩
    · rw [e,q]
      have no : ¬G.Adj (P.first.f k) v := by
        intro d
        rcases (P.first.attached k v vB).mp d.symm with ⟨_,h⟩|⟨_,h⟩
        · exact uv h.symm
        · exact uv h.symm
      exact ⟨fun d=>P.first.off k (by simpa only [d] using vB),
        ⟨fun h=>(no h).elim,fun h=>by omega⟩⟩
    · rw [e,q]
      exact ⟨(P.f_m k l).1,⟨fun d=>((P.f_m k l).2 d).elim,fun h=>by omega⟩⟩
  let LMmap : Fin ((a+1)+(b+1)) → V := Fin.addCases L M
  have nLM : InducedPath G LMmap :=
    concat_induced_paths nL nM (fun i j=>(LM i j).1) (fun i j=>(LM i j).2)
  have lastJoin (i : Fin ((a+1)+(b+1))) (j : Fin c) :
      LMmap i≠R j ∧ (G.Adj (LMmap i) (R j) ↔ i.val+1=(a+1)+(b+1) ∧ j.val=0) := by
    refine Fin.addCases ?_ ?_ i
    · intro x
      simp only [LMmap,Fin.addCases_left]
      have bound := x.isLt
      change L x≠R j ∧ (G.Adj (L x) (R j) ↔ x.val+1=(a+1)+(b+1) ∧ j.val=0)
      rcases aview x with ⟨_,e⟩|⟨k,_,e⟩
      · rw [e]
        exact ⟨fun h=>P.last.off _ (by simpa only [h] using uB),⟨fun d=>(Rnotu j d).elim,fun h=>by omega⟩⟩
      · rw [e]
        exact ⟨(P.f_l k (castC j)).1,
          ⟨fun d=>((P.f_l k (castC j)).2 d).elim,fun h=>by omega⟩⟩
    · intro x
      simp only [LMmap,Fin.addCases_right]
      change M x≠R j ∧ (G.Adj (M x) (R j) ↔ (a+1)+x.val+1=(a+1)+(b+1) ∧ j.val=0)
      rcases bview x with ⟨val,e⟩|⟨k,val,e⟩
      · rw [e,val,Rfirst]
        exact ⟨fun h=>P.last.off _ (by simpa only [h] using vB),by simp [Nat.add_assoc]⟩
      · rw [e,val]
        have kb := k.isLt
        exact ⟨(P.m_l k (castC j)).1,
          ⟨fun d=>((P.m_l k (castC j)).2 d).elim,fun h=>by omega⟩⟩
  have out := concat_induced_paths nLM nR (fun i j=>(lastJoin i j).1) (fun i j=>(lastJoin i j).2)
  have size : P.first.n+P.mid.n+P.last.n = ((a+1)+(b+1))+c := by change _ = _; dsimp [b]; omega
  rw [size]
  exact ⟨_,out⟩

#print axioms DumbRelays.long_path
end Graffiti133Bicycle
