import BicycleRotate133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133NoFive
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem hole_singleton_extension_has_nine {rows d2 : List Nat} {n : Nat}
    (hn : 1≤n) (h4 : FourCycleFree G) (H : Hole G 7)
    (f : Fin n → V) (inj : Function.Injective f) (outer : ∀ i, Outside H.c (f i))
    (site : Fin n → Fin 7) (attach : ∀ i j, G.Adj (f i) (H.c j) ↔ site i=j)
    (edges : ∀ i j, G.Adj (f i) (f j) ↔ bit rows i.val j.val=true)
    (dist2 : ∀ i j : Fin n, bit d2 i.val j.val=true →
      ∃ k : Fin n, bit rows i.val k.val=true ∧ bit rows j.val k.val=true)
    {data : List (List Nat)} (ok : verify rows d2 data (n-1) 0 [0]=true) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  let val (i : Nat) := if h : i < 7 then H.c ⟨i,h⟩ else
    if h : i < 7+n then f ⟨i-7,by omega⟩ else H.c 0
  have old (i : Nat) (hi : i<7) : val i=H.c ⟨i,hi⟩ := dif_pos hi
  have new (i : Fin n) : val (7+i.val)=f i := by
    simp only [val,dif_neg (show ¬7+i.val<7 by omega),
      dif_pos (Nat.add_lt_add_left i.isLt 7)]
    congr 1
    apply Fin.ext
    simp
  let lab (i : Nat) : Nat := if h : i<n then (site ⟨i,h⟩).val else 0
  have lab_eq (i : Nat) (hi : i<n) : lab i=(site ⟨i,hi⟩).val := dif_pos hi
  let M : Numbered G rows d2 n lab :=
    { f := val
      inj := by
        intro i hi j hj e
        by_cases ia : i<7 <;> by_cases ja : j<7
        · rw [old i ia,old j ja] at e
          exact congrArg Fin.val (H.inj e)
        · let j' : Fin n := ⟨j-7,by omega⟩
          have ej : 7+j'.val=j := by dsimp [j']; omega
          rw [old i ia,←ej,new j'] at e
          exact (outer j' ⟨i,ia⟩ e.symm).elim
        · let i' : Fin n := ⟨i-7,by omega⟩
          have ei : 7+i'.val=i := by dsimp [i']; omega
          rw [old j ja,←ei,new i'] at e
          exact (outer i' ⟨j,ja⟩ e).elim
        · let i' : Fin n := ⟨i-7,by omega⟩
          let j' : Fin n := ⟨j-7,by omega⟩
          have ei : 7+i'.val=i := by dsimp [i']; omega
          have ej : 7+j'.val=j := by dsimp [j']; omega
          rw [←ei,←ej,new i',new j'] at e
          rw [←ei,←ej,inj e]
      siteRange := by
        intro i hi
        rw [lab_eq i hi]
        exact Fin.isLt _
      cycleAdj := by
        intro i hi j hj
        rw [old i hi,old j hj,H.adj]
        simp [cycle,Cyclic]
      exteriorAdj := by
        intro i hi j hj
        rw [new ⟨i,hi⟩,new ⟨j,hj⟩]
        exact edges ⟨i,hi⟩ ⟨j,hj⟩
      joinAdj := by
        intro i hi j hj
        rw [new ⟨i,hi⟩,old j hj,lab_eq i hi,attach]
        exact ⟨fun e => congrArg Fin.val e, fun e => Fin.ext e⟩
      distanceTwo := by
        intro i hi j hj e
        obtain ⟨k,a,b⟩ := dist2 ⟨i,hi⟩ ⟨j,hj⟩ e
        exact ⟨k.val,k.isLt,a,b⟩ }
  exact M.force_of_certificate h4 hn ok

#print axioms hole_singleton_extension_has_nine
end Graffiti133Bicycle
