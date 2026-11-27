import GraphPathLift
import ThreeSide189
namespace Graffiti189SingletonCage
open SimpleGraph SimpleGraph.Walk Finset GraphPathLift
variable {n : ℕ}

structure Atom (n : ℕ) where
  two : Bool
  a : Fin n
  b : Fin n
  deriving DecidableEq

def norm (two : Bool) (i j : Fin n) : Atom n :=
  if i≤j then ⟨two,i,j⟩ else ⟨two,j,i⟩

noncomputable def eval (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Atom n) : Bool :=
  if a.two then decide (G.dist a.a a.b=2) else decide (G.Adj a.a a.b)

@[simp] theorem eval_edge_true (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    eval G (norm false u v)=true ↔ G.Adj u v := by
  by_cases h : u≤v <;> simp [norm,h,eval,G.adj_comm v u]
@[simp] theorem eval_edge_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    eval G (norm false u v)=false ↔ ¬G.Adj u v := by
  by_cases h : u≤v <;> simp [norm,h,eval,G.adj_comm v u]
@[simp] theorem eval_two_true (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    eval G (norm true u v)=true ↔ G.dist u v=2 := by
  by_cases h : u≤v <;> simp [norm,h,eval,(show G.dist v u=G.dist u v from G.dist_comm)]
@[simp] theorem eval_two_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    eval G (norm true u v)=false ↔ ¬G.dist u v=2 := by
  by_cases h : u≤v <;> simp [norm,h,eval,(show G.dist v u=G.dist u v from G.dist_comm)]

inductive Row (n : ℕ)
  | fixed : Fin n → Fin n → Bool → Row n
  | two : Fin n → Fin n → Fin n → Row n
  | shell : Fin n → List (Fin n) → Row n
  | degree : Fin n → List (Fin n) → Row n
  | cut : Option (Fin n) → List (Fin n) → List (Fin n) → Row n
  | path : List (Fin n) → Row n

def occ (v : Option (Fin n)) (x : Fin n) : Prop := v ≠ some x
instance (v : Option (Fin n)) (x : Fin n) : Decidable (occ v x) := by unfold occ; infer_instance

def badLits : Row n → List (Atom n × Bool)
  | .fixed i j b => [(norm false i j,!b)]
  | .two i j w => [(norm false i w,true),(norm false w j,true),
      (norm false i j,false),(norm true i j,false)]
  | .shell i js => js.map (fun j=>(norm true i j,true))
  | .degree i js => js.map (fun j=>(norm false i j,false))
  | .cut _ L R => L.flatMap fun i=>R.map fun j=>(norm false i j,false)
  | .path P => (edgePairs P).map fun (i,j)=>(norm false i j,true)

def wanted {n : ℕ} (x y : ℕ) (ab : Bool) (i j : Fin n) : Option Bool :=
  if i.val = 0 then some (decide (j.val=1 ∨ j.val=2))
  else if i.val=1 ∧ j.val=2 then some ab
  else if i.val=1 ∨ i.val=2 then
    let code := if j.val<3+x then 1 else if j.val<3+x+y then 2 else if j.val<7 then 3 else 0
    some (decide (code=i.val ∨ code=3))
  else none

def valid (x y : ℕ) (ab : Bool) : Row n → Prop
  | .fixed i j b => i<j ∧ wanted x y ab i j = some b
  | .two i j _ => i≠j
  | .shell _ js => 5≤js.toFinset.card
  | .degree i js => i.val≠0 ∧ 1≤n ∧ n-4≤js.toFinset.card ∧ i∉js
  | .cut v L R => L≠[] ∧ R≠[] ∧
      (∀ i, i∈L → i∉R ∧ occ v i) ∧ (∀ i, i∈R → occ v i) ∧
      (∀ i, occ v i → i∈L ∨ i∈R)
  | .path P => P≠[] ∧ P.Nodup ∧ ∀ i, i∈P

instance (x y : ℕ) (ab : Bool) (row : Row n) : Decidable (valid x y ab row) := by
  cases row <;> dsimp [valid] <;> infer_instance

private theorem forced_cross (G : SimpleGraph (Fin n))
    (hc : ∀ v : Option (Fin n), (G.induce (occ v)).Connected)
    (v : Option (Fin n)) (L R : List (Fin n)) (lne : L≠[]) (rne : R≠[])
    (dis : ∀ i, i∈L → i∉R ∧ occ v i) (rin : ∀ i, i∈R → occ v i)
    (cover : ∀ i, occ v i → i∈L ∨ i∈R)
    (none : ∀ i∈L, ∀ j∈R, ¬G.Adj i j) : False := by
  obtain ⟨l,lL⟩ : ∃ l,l∈L := by cases L with
    | nil => contradiction
    | cons u t => exact ⟨u,by simp⟩
  obtain ⟨r,rR⟩ : ∃ r,r∈R := by cases R with
    | nil => contradiction
    | cons u t => exact ⟨u,by simp⟩
  obtain ⟨p⟩ := hc v ⟨l,(dis l lL).2⟩ ⟨r,rin r rR⟩
  have preserve {i j : {x // occ v x}} (q : (G.induce (occ v)).Walk i j)
      (hi : i.val∈L) : j.val∈L := by
    induction q with
    | nil => exact hi
    | @cons i k j e q ih =>
      apply ih
      rcases cover k.val k.prop with yes|no
      · exact yes
      · exact (none i.val hi k.val no e).elim
  exact (dis r (preserve p lL)).1 rR

/-- Verify an input clause from graph facts, without trusting the SAT encoding. -/
theorem sound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x y : ℕ) (ab : Bool)
    (hc : G.Connected)
    (cuts : ∀ v : Option (Fin n), (G.induce (occ v)).Connected)
    (fixed : ∀ i j b, i<j → wanted x y ab i j=some b → decide (G.Adj i j)=b)
    (degree : ∀ i, i.val≠0 → 4≤G.degree i)
    (d2 : ∀ i, (Graffiti189LongestPath.DistanceTwo G i).card≤4)
    (no : ¬ GraphPathLift.HasSpanningPath G)
    (row : Row n) (vr : valid x y ab row)
    (fail : ∀ p∈badLits row, eval G p.1=p.2) : False := by
  cases row with
  | fixed i j b =>
    obtain ⟨ij,w⟩ := vr
    have h := fail (norm false i j,!b) (by simp [badLits])
    have f := fixed i j b ij w
    cases b
    · exact (of_decide_eq_false f) ((eval_edge_true G i j).mp h)
    · exact (eval_edge_false G i j).mp h (of_decide_eq_true f)
  | two i j w =>
    have a := (eval_edge_true G i w).mp (fail (norm false i w,true) (by simp [badLits]))
    have b := (eval_edge_true G w j).mp (fail (norm false w j,true) (by simp [badLits]))
    have c := (eval_edge_false G i j).mp (fail (norm false i j,false) (by simp [badLits]))
    have e := (eval_two_false G i j).mp (fail (norm true i j,false) (by simp [badLits]))
    exact e (Graffiti189LongestPath.FourCut.Three.Sides.dist_two hc vr c a b)
  | shell i js =>
    have sub : js.toFinset ⊆ Graffiti189LongestPath.DistanceTwo G i := by
      intro j hj
      rw [List.mem_toFinset] at hj
      apply Graffiti189LongestPath.FourCut.Three.Sides.mem_d2.mpr
      exact (eval_two_true G i j).mp (fail (norm true i j,true) (by simpa [badLits] using
        (List.mem_map_of_mem (f:=fun j=>(norm true i j,true)) hj)))
    have k := (card_le_card sub).trans (d2 i)
    change 5 ≤ js.toFinset.card at vr
    omega
  | degree i js =>
    obtain ⟨i0,nn,jc,ijn⟩ := vr
    have sub : G.neighborFinset i ⊆ univ \ insert i js.toFinset := by
      intro j hj
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro f
      have hj' := (G.mem_neighborFinset i j).mp hj
      rcases mem_insert.mp f with rfl|q
      · exact G.loopless _ hj'
      have e := (eval_edge_false G i j).mp (fail (norm false i j,false) (by
        change (norm false i j,false) ∈ js.map _
        apply List.mem_map_of_mem; simpa using q))
      exact e hj'
    have hh := card_le_card sub
    rw [card_neighborFinset_eq_degree] at hh
    have eq := card_sdiff_add_card_eq_card (show insert i js.toFinset ⊆ univ from subset_univ _)
    rw [card_univ,Fintype.card_fin,card_insert_of_not_mem (by simpa using ijn)] at eq
    have d := degree i i0
    omega
  | cut v L R =>
    obtain ⟨lne,rne,dis,rin,cvr⟩ := vr
    apply forced_cross G cuts v L R lne rne dis rin cvr
    intro i hi j hj
    apply (eval_edge_false G i j).mp
    apply fail (norm false i j,false)
    simpa only [badLits,List.mem_flatMap] using
      (show ∃ k∈L, (norm false i j,false) ∈ R.map (fun j=>(norm false k j,false)) from
        ⟨i,hi,List.mem_map_of_mem hj⟩)
  | path P =>
    obtain ⟨pne,nd,all⟩ := vr
    apply no
    apply spanningPath_of_list G P pne nd all
    intro p hp
    apply (eval_edge_true G p.1 p.2).mp
    exact fail (norm false p.1 p.2,true) (by simpa only [badLits] using
      (List.mem_map_of_mem (f:=fun (i,j)=>(norm false i j,true)) hp))

#print axioms sound
end Graffiti189SingletonCage
