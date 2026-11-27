import RemoteCycleChainCover
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteRungLadder
open RemoteSubdivisionCore (Marks)
open RemoteCycleChain (weave label label_hit label_none Traverses label_iff_traverses
  labels_weave old_weave weave_nodup weave_path)

theorem spanning_route_factor {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} (M : Marks G I)
    (P : List V) (distinct : P.Nodup) (path : P.Chain' G.Adj)
    (old : ∀ v,v∈P) (marks : ∀ i,Traverses M i P)
    (mod3 : 3∣Fintype.card V+Fintype.card I) : SquareCap.HasFactor M.expanded := by
  have nod := weave_nodup M (label M) (label_hit M) distinct
  have walk := weave_path M (label M) (label_hit M) (fun _ h=>label_none M h) path
  have all : (weave (label M) P).toFinset=univ := by
    apply eq_univ_of_forall
    rintro (v|i)
    · exact List.mem_toFinset.mpr ((old_weave _ v P).mpr (old v))
    · exact List.mem_toFinset.mpr ((labels_weave _ i P).mpr
        ((label_iff_traverses M i P).mpr (marks i)))
  have order : (weave (label M) P).length = Fintype.card V+Fintype.card I := by
    rw [←List.toFinset_card_of_nodup nod,all,card_univ,Fintype.card_sum]
  change SquareCap.FactorOn M.expanded univ
  rw [←all]
  exact RemoteGapRunPacking.run_factor _ nod walk (order.symm ▸ mod3)

private theorem pair_at_traversed {V I : Type*} {G : SimpleGraph V}
    (M : Marks G I) {i : I} :
    ∀ (j : ℕ) (P : List V) (hj : j+1<P.length),
    M.Pair i (P.get ⟨j,by omega⟩) (P.get ⟨j+1,hj⟩) → Traverses M i P := by
  intro j
  induction j with
  | zero =>
    intro P hj hp
    match P with
    | [] => simp at hj
    | [_] => simp at hj
    | a::b::R => exact Or.inl hp
  | succ j ih =>
    intro P hj hp
    cases P with
    | nil => simp at hj
    | cons a Q =>
      cases Q with
      | nil => simp at hj
      | cons b R =>
        apply Or.inr
        exact ih (b::R) (Nat.lt_of_succ_lt_succ hj) hp

private theorem chain_tabulated {V : Type*} {n : ℕ} {f : Fin n→V} {r : V→V→Prop}
    (next : ∀ (i : ℕ) (h : i+1<n),r (f ⟨i,by omega⟩) (f ⟨i+1,h⟩)) :
    (List.ofFn f).Chain' r := by
  simp_rw [List.chain'_iff_get,List.get_ofFn,List.length_ofFn]
  exact fun i hi=>next i (by omega)

private def row (j : ℕ) : Bool := decide (((j+1)/2)%2=1)

private theorem row_same (j : ℕ) (odd : j%2=1) : row j=row (j+1) := by
  have e : (j+1)/2=(j+2)/2 := by omega
  change decide (((j+1)/2)%2=1)=decide (((j+2)/2)%2=1)
  rw [e]

private theorem row_flip (j : ℕ) (even : j%2=0) : row j≠row (j+1) := by
  have e : (j+2)/2=(j+1)/2+1 := by omega
  have d : ((j+1)/2)%2≠((j+2)/2)%2 := by omega
  intro eq
  by_cases h : ((j+1)/2)%2=1
  · have h' : ((j+2)/2)%2≠1 := fun hh=>d (h.trans hh.symm)
    have db : row j=true := by simp [row,h]
    have db' : row (j+1)=false := by change decide (((j+2)/2)%2=1)=false; exact decide_eq_false h'
    simp [db,db'] at eq
  · have h' : ((j+2)/2)%2=1 := by omega
    have db : row j=false := by simp [row,h]
    have db' : row (j+1)=true := by change decide (((j+2)/2)%2=1)=true; exact decide_eq_true h'
    simp [db,db'] at eq

def zigzag (n : ℕ) (j : Fin (2*n)) : Fin n×Bool :=
  (⟨j.val/2, by have z:=j.isLt; omega⟩, row j.val)

private theorem zigzag_inj (n : ℕ) : Function.Injective (zigzag n) := by
  intro i j eq
  have col : i.val/2=j.val/2 := congrArg (fun z : Fin n×Bool=>z.1.val) eq
  have rr : row i.val=row j.val := congrArg Prod.snd eq
  by_cases same : i.val=j.val
  · exact Fin.ext same
  · exfalso
    have bef : (i.val+1=j.val ∧ i.val%2=0) ∨ (j.val+1=i.val ∧ j.val%2=0) := by omega
    rcases bef with ⟨e,ei⟩|⟨e,ei⟩
    · exact row_flip i.val ei (e.symm ▸ rr)
    · exact row_flip j.val ei (e.symm ▸ rr.symm)

private theorem zigzag_suj (n : ℕ) : Function.Surjective (zigzag n) := by
  rintro ⟨c,b⟩
  have lt0 : 2*c.val<2*n := by have cc:=c.isLt; omega
  have lt1 : 2*c.val+1<2*n := by have cc:=c.isLt; omega
  have e : row (2*c.val)≠row (2*c.val+1) := row_flip _ (by omega)
  have one : row (2*c.val)=b ∨ row (2*c.val+1)=b := by
    cases b <;> cases x : row (2*c.val) <;> cases y : row (2*c.val+1) <;> simp_all
  rcases one with h|h
  · exact ⟨⟨2*c.val,lt0⟩,Prod.ext (Fin.ext (by change 2*c.val/2=c.val; omega)) h⟩
  · exact ⟨⟨2*c.val+1,lt1⟩,Prod.ext (Fin.ext (by change (2*c.val+1)/2=c.val; omega)) h⟩

/-- One alternate rail per successive pair of columns suffices. All
independently subdivided rungs are traversed by the same zigzag. -/
theorem factor_of_spanning_ladder {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {G : SimpleGraph (Fin n×Bool)} (M : Marks G I)
    (vertical : ∀ c,G.Adj (c,false) (c,true))
    (rail : ∀ (j : ℕ) (hj : j+1<n),
      G.Adj (⟨j,by omega⟩,row (2*j+1)) (⟨j+1,hj⟩,row (2*j+1)))
    (marks : ∀ i,(M.a i).1=(M.b i).1)
    (mod3 : 3∣2*n+Fintype.card I) : SquareCap.HasFactor M.expanded := by
  let L := List.ofFn (zigzag n)
  have nd : L.Nodup := List.nodup_ofFn.mpr (zigzag_inj n)
  have spans : ∀ x,x∈L := fun x=>List.mem_ofFn.mpr (zigzag_suj n x)
  have route : L.Chain' G.Adj := by
    apply chain_tabulated
    intro j jh
    by_cases eq : j%2=0
    · have c : j/2=(j+1)/2 := by omega
      have r := row_flip j eq
      let col : Fin n := ⟨j/2,by omega⟩
      change G.Adj (col,row j) (⟨(j+1)/2,by omega⟩,row (j+1))
      have col_eq : (⟨(j+1)/2,by omega⟩:Fin n)=col := Fin.ext c.symm
      rw [col_eq]
      cases p : row j <;> cases q : row (j+1)
      · exact (r (p.trans q.symm)).elim
      · exact vertical col
      · exact (vertical col).symm
      · exact (r (p.trans q.symm)).elim
    · have od : j%2=1 := by omega
      have c : (j+1)/2=j/2+1 := by omega
      have o : 2*(j/2)+1=j := by omega
      have r := row_same j od
      show G.Adj (⟨j/2,by omega⟩,row j) (⟨(j+1)/2,by omega⟩,row (j+1))
      have col_eq : (⟨(j+1)/2,by omega⟩:Fin n)=⟨j/2+1,by omega⟩ := Fin.ext c
      rw [col_eq,←r]
      simpa only [o] using rail (j/2) (by omega)
  have reaches : ∀ i,Traverses M i L := by
    intro i
    let c := (M.a i).1
    have cc := c.isLt
    have lt : 2*c.val+1<L.length := by simp only [L,List.length_ofFn]; omega
    apply pair_at_traversed M (2*c.val) L lt
    simp only [L,List.get_ofFn]
    have col₀ : (⟨2*c.val/2,by omega⟩:Fin n)=c := Fin.ext (by change 2*c.val/2=c.val; omega)
    have col₁ : (⟨(2*c.val+1)/2,by omega⟩:Fin n)=c := Fin.ext (by change (2*c.val+1)/2=c.val; omega)
    change M.Pair i (⟨2*c.val/2,by omega⟩,row (2*c.val))
      (⟨(2*c.val+1)/2,by omega⟩,row (2*c.val+1))
    rw [col₀,col₁]
    have ra : row (2*c.val)≠row (2*c.val+1) := row_flip _ (by omega)
    have ca : (M.a i).1 = c := rfl
    have cb : (M.b i).1 = c := (marks i).symm
    have opp : (M.a i).2≠(M.b i).2 :=
      fun e=>(M.edge i).ne (Prod.ext (marks i) e)
    have pair (p q : Bool) (hp : p≠q) : M.Pair i (c,p) (c,q) := by
      have arow (r : Bool) (e : r=(M.a i).2) : (c,r)=M.a i := Prod.ext ca.symm e
      have brow (r : Bool) (e : r=(M.b i).2) : (c,r)=M.b i := Prod.ext cb.symm e
      have test : ∀ u v a b : Bool,u≠v → a≠b →
          (u=a∧v=b)∨(u=b∧v=a) := by decide
      rcases test p q (M.a i).2 (M.b i).2 hp opp with ⟨e,f⟩|⟨e,f⟩
      · exact Or.inl ⟨arow p e,brow q f⟩
      · exact Or.inr ⟨brow p e,arow q f⟩
    exact pair _ _ ra
  apply spanning_route_factor M L nd route spans reaches
  simpa [Fintype.card_prod,Nat.mul_comm] using mod3

/-- The clean graph-theoretic condition only asks for a spanning ladder
subgraph and that each subdivided edge be one of its rungs. -/
theorem factor_of_any_rung_subdivisions {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {G : SimpleGraph (Fin n×Bool)} (M : Marks G I)
    (vertical : ∀ c,G.Adj (c,false) (c,true))
    (rails : ∀ (j : ℕ) (hj : j+1<n) (b : Bool),
      G.Adj (⟨j,by omega⟩,b) (⟨j+1,hj⟩,b))
    (marks : ∀ i,(M.a i).1=(M.b i).1)
    (mod3 : 3∣2*n+Fintype.card I) : SquareCap.HasFactor M.expanded :=
  factor_of_spanning_ladder M vertical (fun j hj=>rails j hj _) marks mod3

#print axioms spanning_route_factor
#print axioms factor_of_any_rung_subdivisions
end KelmansCactus.AtomicBridge.RemoteRungLadder
