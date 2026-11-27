import P5CliqueOnePortAmbientBudget133
import Mathlib.Data.Finset.Max

namespace Graffiti133P5CliqueArms
open SimpleGraph Graffiti133 Graffiti133Camby
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} {G : SimpleGraph V}

def IsCleanPortStem (D : Finset V) (p : Fin 4→V) (i j : Fin 4) (d : Nat) : Prop :=
  ∃ f : Fin (d+1)→V, InducedPath G f ∧ (∀ k,f k∈D) ∧ f 0=p i ∧
    f (Fin.last d)=p j ∧ ∀ k, 0<k.val → k.val<d → ∀ c,f k≠p c

/-- A nearest clean stem is induced, avoids other ports internally,
and can meet any extra port only from its terminal internal vertex. -/
def IsNearestPortStem (D : Finset V) (p : Fin 4→V) (i j : Fin 4) (d : Nat) : Prop :=
  ∃ f : Fin (d+1)→V, InducedPath G f ∧ (∀ k,f k∈D) ∧ f 0=p i ∧
    f (Fin.last d)=p j ∧ (∀ k, 0<k.val → k.val<d → ∀ c,f k≠p c) ∧
    ∀ k, k.val<d → ∀ c≠i,G.Adj (f k) (p c)→d≤k.val+1

private theorem takeLen {u v : V} (P : G.Walk u v) (i : Nat) (hi : i≤P.length) :
    (P.take i).length=i := by
  induction P generalizing i with
  | nil =>
    have e : i=0 := by simpa using hi
    subst i
    rfl
  | cons h q ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (q.take i).length+1=i+1
      rw [ih i (by simp only [Walk.length_cons] at hi; omega)]

private theorem dropLen {u v : V} (P : G.Walk u v) (i : Nat) :
    (P.drop i).length=P.length-i := by
  induction P generalizing i with
  | nil => cases i <;> simp [Walk.drop]
  | cons h q ih =>
    cases i with
    | zero => simp [Walk.drop]
    | succ i =>
      change (q.drop i).length=(q.length+1)-(i+1)
      rw [ih i,Nat.add_sub_add_right]

/-- Each label has a clean shortest route in the core to some other port;
it stops before meeting any additional port and has two through five edges. -/
theorem each_has_nearest_clean_port_stem
    (D : Finset V) (p : Fin 4→V) (pm : ∀ j,p j∈D) (pi : Function.Injective p)
    (pind : ∀ i j,¬G.Adj (p i) (p j))
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (i : Fin 4) :
    ∃ j : Fin 4, j≠i ∧ ∃ d : Nat, 2≤d ∧ d≤5 ∧ IsNearestPortStem (G:=G) D p i j d := by
  classical
  let H := G.induce (D : Set V)
  have ch : H.Connected := hc
  let a (j : Fin 4) : (D : Set V) := ⟨p j,pm j⟩
  let F := (Finset.univ : Finset (Fin 4)).erase i
  have non : F.Nonempty := by
    have o : ∀ i : Fin 4,∃ j : Fin 4,j≠i := by decide
    obtain ⟨j,e⟩ := o i
    exact ⟨j,Finset.mem_erase.mpr ⟨e,Finset.mem_univ _⟩⟩
  obtain ⟨j,jF,near⟩ := Finset.exists_min_image F (fun k=>H.dist (a i) (a k)) non
  have ij : j≠i := (Finset.mem_erase.mp jF).1
  have ne : a i≠a j := fun e=>ij (pi (congrArg Subtype.val e)).symm
  obtain ⟨w,wd⟩ := ch.exists_walk_length_eq_dist (a i) (a j)
  change w.length = H.dist (a i) (a j) at wd
  have dlo : 2≤w.length := by
    have pos : w.length≠0 := fun e=>ne (ch.dist_eq_zero_iff.mp (wd.symm.trans e))
    have neq : w.length≠1 := by
      intro e
      have h : H.Adj (a i) (a j) := SimpleGraph.dist_eq_one_iff_adj.mp (wd.symm.trans e)
      exact pind i j h
    omega
  let f (k : Fin (w.length+1)) := w.getVert k
  have level (k : Fin (w.length+1)) : H.dist (a i) (f k)=k.val := by
    have hi := H.dist_le (w.take k.val)
    rw [takeLen w k.val (by omega)] at hi
    have hj := H.dist_le (w.drop k.val)
    rw [dropLen] at hj
    have ht := ch.dist_triangle (u:=a i) (v:=f k) (w:=a j)
    change H.dist (a i) (f k)≤k.val at hi
    change H.dist (f k) (a j)≤w.length-k.val at hj
    omega
  have geo : InducedPath H f := by
    constructor
    · intro x y e
      apply Fin.ext
      rw [←level x,←level y,e]
    · intro x y xy
      constructor
      · intro e
        have ht := ch.dist_triangle (u:=a i) (v:=f x) (w:=f y)
        rw [level x,level y,SimpleGraph.dist_eq_one_iff_adj.mpr e] at ht
        change x.val<y.val at xy
        omega
      · intro e
        have hi : x.val<w.length := by omega
        have h := w.adj_getVert_succ hi
        change H.Adj (w.getVert x.val) (w.getVert y.val)
        rw [←e]
        exact h
  have dhi : w.length≤5 := by
    by_cases short : w.length≤5
    · exact short
    exfalso
    let k : Fin 7 → Fin (w.length+1) := fun x=>⟨x.val,by have hx:=x.isLt; omega⟩
    apply h7
    refine ⟨f∘k,fun x y eq=>Fin.ext (congrArg (fun z : Fin (w.length+1)=>z.val) (geo.1 eq)),?_⟩
    intro x y xy
    have e : k x<k y := xy
    exact geo.2 _ _ e
  refine ⟨j,ij,w.length,dlo,dhi,fun k=>(f k).val,?_,fun x=>(f x).property,?_,?_,?_,?_⟩
  · refine ⟨fun x y eq=>geo.1 (Subtype.ext eq),?_⟩
    intro x y xy
    exact geo.2 _ _ xy
  · exact congrArg Subtype.val w.getVert_zero
  · exact congrArg Subtype.val w.getVert_length
  · intro k k0 kd c ceq
    have fk : f k=a c := Subtype.ext ceq
    have ci : c≠i := by
      rintro rfl
      have e : f k=f 0 := fk.trans w.getVert_zero.symm
      have kv := congrArg Fin.val (geo.1 e)
      change k.val=0 at kv
      omega
    have upper := H.dist_le (w.take k.val)
    rw [takeLen w k.val (by omega)] at upper
    change H.dist (a i) (f k)≤k.val at upper
    rw [fk] at upper
    have nm := near c (Finset.mem_erase.mpr ⟨ci,Finset.mem_univ _⟩)
    omega
  · intro k _ c ci edge
    have ac : H.Adj (f k) (a c) := edge
    have close := ch.dist_triangle (u:=a i) (v:=f k) (w:=a c)
    rw [level k,SimpleGraph.dist_eq_one_iff_adj.mpr ac] at close
    have nm := near c (Finset.mem_erase.mpr ⟨ci,Finset.mem_univ _⟩)
    omega

theorem nearestPortStem_clean (D : Finset V) (p : Fin 4→V) {i j : Fin 4} {d : Nat}
    (h : IsNearestPortStem (G:=G) D p i j d) : IsCleanPortStem (G:=G) D p i j d := by
  obtain ⟨f,fp,fd,h1,h2,internal,_⟩ := h
  exact ⟨f,fp,fd,h1,h2,internal⟩

#print axioms each_has_nearest_clean_port_stem
end Graffiti133P5CliqueArms
