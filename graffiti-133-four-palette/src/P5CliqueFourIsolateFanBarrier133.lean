import CambyDomBase133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133P5CliqueArms.FourIsolateFanBarrier
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 19000000

def dfs {n : Nat} (adj : Fin n→Fin n→Bool) : Nat→Fin n→List (Fin n)→Bool
  | 0,_,_ => true
  | m+1,v,S =>
      (List.finRange n).any (fun w=>adj v w && !(decide (w∈v::S)) &&
        !(S.any (adj w)) && dfs adj m w (v::S))

theorem dfs_complete {n k : Nat} {G : SimpleGraph (Fin n)} (a : Fin n→Fin n→Bool)
    (aok : ∀ x y,a x y=true ↔ G.Adj x y) (f : Fin k→Fin n) (hf : InducedPath G f)
    (i : Fin k) (m : Nat) (bound : i.val+m<k) (S : List (Fin n))
    (pr : ∀ z∈S,∃ j : Fin k,(j.val < i.val) ∧ f j=z) :
    dfs a m (f i) S=true := by
  induction m generalizing i S with
  | zero => rfl
  | succ m ih =>
    let j : Fin k := ⟨i.val+1,by omega⟩
    have ij : (i.val < j.val) := by simp [j]
    have e : a (f i) (f j)=true := (aok _ _).mpr ((hf.2 i j ij).mpr rfl)
    have nm : f j∉f i::S := by
      intro h
      rcases List.mem_cons.mp h with q|q
      · exact (ne_of_gt ij) (congrArg Fin.val (hf.1 q))
      · obtain ⟨l,li,lq⟩ := pr _ q
        have eq := congrArg Fin.val (hf.1 lq)
        omega
    have ch : S.any (a (f j))=false := by
      cases h : S.any (a (f j)) with
      | false => rfl
      | true =>
        obtain ⟨z,zm,hit⟩ := List.any_eq_true.mp h
        obtain ⟨l,li,rfl⟩ := pr z zm
        have lj : (l.val < j.val) := by omega
        have eq := (hf.2 l j lj).mp ((aok _ _).mp hit).symm
        omega
    have pre (z : Fin n) (zm : z∈f i::S) : ∃ l : Fin k,(l.val < j.val) ∧ f l=z := by
      rcases List.mem_cons.mp zm with rfl|s
      · exact ⟨i,ij,rfl⟩
      · obtain ⟨l,li,e⟩ := pr z s
        exact ⟨l,li.trans ij,e⟩
    have jb : j.val+m<k := by simp [j]; omega
    have tail := ih j jb (f i::S) pre
    apply List.any_eq_true.mpr
    exact ⟨f j,List.mem_finRange _,by simp [e,nm,ch,tail]⟩


abbrev V := Fin 12

def edges : List (V×V) :=
  [(1,4),(2,4),(0,5),(4,5),(3,6),(4,7),(6,7),(0,8),(1,9),(8,9),(2,10),(8,10),(3,11),(8,11)]

def adjB (x y : V) : Bool := decide ((x,y)∈edges ∨ (y,x)∈edges)

def graph : SimpleGraph V where
  Adj x y := adjB x y=true
  symm := by
    intro x y h
    have q : (x,y)∈edges ∨ (y,x)∈edges := of_decide_eq_true h
    exact decide_eq_true q.symm
  loopless := by
    change ∀ x : V, ¬ adjB x x=true
    decide

instance : DecidableRel graph.Adj := fun x y=>inferInstanceAs (Decidable (adjB x y=true))

def D : Finset V := {0,1,2,3,4,5,6,7}
def P : Finset V := {0,1,2,3}

theorem four_free : FourCycleFree graph := by
  have h : ∀ a b : V,a≠b→
      ((Finset.univ : Finset V).filter fun x=>graph.Adj a x ∧ graph.Adj b x).card≤1 := by decide
  intro a b x y ab ax bx ay byy
  exact Finset.card_le_one.mp (h a b ab) x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ax,bx⟩)
    y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ay,byy⟩)

theorem no_P9 : NoPath graph 9 := by
  have b : (List.finRange 12).any (fun x=>dfs adjB 8 x [])=false := by decide
  rintro ⟨f,h⟩
  have d := dfs_complete adjB (fun _ _=>Iff.rfl) f h (0:Fin 9) 8 (by decide) [] (by simp)
  have t : (List.finRange 12).any (fun x=>dfs adjB 8 x [])=true :=
    List.any_eq_true.mpr ⟨f 0,List.mem_finRange _,d⟩
  rw [b] at t
  contradiction

def connectedStep (T : Finset V) : Nat→V→V→Bool
  | 0,u,v => decide (u=v)
  | k+1,u,v => decide (u=v) ||
      (List.finRange 12).any (fun w=>decide (w∈T) && adjB u w && connectedStep T k w v)

theorem connectedStep_sound {T : Finset V} {k : Nat} {u v : V} (uM : u∈T) (vM : v∈T)
    (h : connectedStep T k u v=true) :
    ∃ p : (graph.induce (T : Set V)).Walk ⟨u,uM⟩ ⟨v,vM⟩,p.length≤k := by
  induction k generalizing u with
  | zero =>
    have e : u=v := of_decide_eq_true h
    subst v
    exact ⟨.nil,by simp⟩
  | succ k ih =>
    simp only [connectedStep,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with e|e
    · subst v
      exact ⟨.nil,by simp⟩
    obtain ⟨w,_,hw⟩ := List.any_eq_true.mp e
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hw
    obtain ⟨q,hq⟩ := ih hw.1.1 hw.2
    have a : (graph.induce (T : Set V)).Adj ⟨u,uM⟩ ⟨w,hw.1.1⟩ := hw.1.2
    exact ⟨.cons a q,by simp; omega⟩

theorem connectedStep_complete {T : Finset V} {u v : (T : Set V)}
    (p : (graph.induce (T : Set V)).Walk u v) (k : Nat) (hk : p.length≤k) :
    connectedStep T k u.val v.val=true := by
  induction p generalizing k with
  | nil =>
    cases k <;> simp [connectedStep]
  | @cons x y z e w ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      simp only [connectedStep,Bool.or_eq_true,decide_eq_true_eq]
      right
      apply List.any_eq_true.mpr
      refine ⟨y.val,List.mem_finRange _,?_⟩
      have adj : adjB x.val y.val=true := e
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨⟨y.property,adj⟩,ih k (by simp at hk; omega)⟩

theorem connectedStep_of_connected {T : Finset V}
    (h : (graph.induce (T : Set V)).Connected) :
    ∀ u∈T,∀ v∈T,connectedStep T (T.card-1) u v=true := by
  intro u um v vm
  obtain ⟨p,hp⟩ := (h ⟨u,um⟩ ⟨v,vm⟩).exists_isPath
  have t := hp.length_lt
  have e : Fintype.card (T : Set V)=T.card := Fintype.card_coe _
  exact connectedStep_complete p _ (by rw [e] at t; omega)

theorem connected_of_connectedStep {T : Finset V} (n : Nat) (ne : T.Nonempty)
    (h : ∀ u∈T,∀ v∈T,connectedStep T n u v=true) :
    (graph.induce (T : Set V)).Connected := by
  obtain ⟨u,um⟩ := ne
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u,um⟩,fun v=>?_⟩
  obtain ⟨p,_⟩ := connectedStep_sound um v.property (h u um v.val v.property)
  exact ⟨p⟩

private def allSet : Finset V := Finset.univ

private theorem mem_allSet (x : V) : x∈allSet := Finset.mem_univ x

private def forget (T : Finset V) : graph.induce (T : Set V) →g graph :=
  ⟨Subtype.val,fun e=>e⟩

private def toAll : graph →g graph.induce (allSet : Set V) :=
  ⟨fun x=>⟨x,mem_allSet x⟩,fun e=>e⟩

private theorem all_four_steps : ∀ x y : V,connectedStep allSet 4 x y=true := by decide

theorem connected : graph.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0,fun x=>?_⟩
  obtain ⟨p,_⟩ := connectedStep_sound (mem_allSet 0) (mem_allSet x) (all_four_steps 0 x)
  exact ⟨p.map (forget allSet)⟩

private def far (x : V) : V := (![6,3,3,5,11,3,0,8,7,6,6,4] : Fin 12→V) x

theorem radius_eq_four : radius graph=4 := by
  have bound₁ (x y : V) : graph.dist x y≤4 := by
    obtain ⟨p,pl⟩ := connectedStep_sound (mem_allSet x) (mem_allSet y) (all_four_steps x y)
    exact (graph.dist_le (p.map (forget allSet))).trans (by simpa using pl)
  have fails : ∀ x : V,connectedStep allSet 3 x (far x)=false := by decide
  have bound₂ (x : V) : 4≤graph.dist x (far x) := by
    by_contra n
    obtain ⟨p,pl⟩ := connected.exists_walk_length_eq_dist x (far x)
    have le : (p.map toAll).length≤3 := by simp; omega
    have ok := connectedStep_complete (p.map toAll) 3 le
    change connectedStep allSet 3 x (far x)=true at ok
    rw [fails x] at ok
    contradiction
  have eq (x : V) : Finset.univ.sup (graph.dist x)=4 :=
    le_antisymm (Finset.sup_le_iff.mpr (fun y _=>bound₁ x y))
      ((bound₂ x).trans (Finset.le_sup (f:=graph.dist x) (Finset.mem_univ (far x))))
  have im : (Finset.univ.image fun u=>Finset.univ.sup (graph.dist u))={4} := by
    ext n
    constructor
    · intro nm
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp nm
      simp [eq v]
    · intro nm
      have ne : n=4 := Finset.mem_singleton.mp nm
      exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,(eq 0).trans ne.symm⟩
  unfold radius
  rw [im]
  rfl

theorem core_connected : (graph.induce (D : Set V)).Connected := by
  apply connected_of_connectedStep 7 (show D.Nonempty by decide)
  decide

def coreAdj (x y : V) : Bool := decide (x∈D ∧ y∈D) && adjB x y

def corePad : SimpleGraph V where
  Adj x y := x∈D ∧ y∈D ∧ graph.Adj x y
  symm := by
    intro x y h
    exact ⟨h.2.1,h.1,h.2.2.symm⟩
  loopless := fun _ h=>graph.loopless _ h.2.2

theorem core_no_P7 : NoPath (graph.induce (D : Set V)) 7 := by
  have cert : (List.finRange 12).any (fun x=>dfs coreAdj 6 x [])=false := by decide
  rintro ⟨f,h⟩
  let e (i : Fin 7) := (f i).val
  have he : InducedPath corePad e := by
    refine ⟨fun i j eq=>h.1 (Subtype.ext eq),?_⟩
    intro i j ij
    exact (show corePad.Adj (e i) (e j) ↔ (graph.induce (D : Set V)).Adj (f i) (f j) from
      ⟨fun z=>z.2.2,fun z=>⟨(f i).property,(f j).property,z⟩⟩).trans (h.2 i j ij)
  have aok : ∀ x y, coreAdj x y=true ↔ corePad.Adj x y := by
    intro x y
    change ((decide (x∈D ∧ y∈D) && adjB x y)=true) ↔ x∈D ∧ y∈D ∧ adjB x y=true
    simp [and_assoc]
  have b := dfs_complete coreAdj aok e he (0:Fin 7) 6 (by decide) [] (by simp)
  have z : (List.finRange 12).any (fun x=>dfs coreAdj 6 x [])=true :=
    List.any_eq_true.mpr ⟨e 0,List.mem_finRange _,b⟩
  rw [cert] at z
  contradiction

theorem four_isolated_ports :
    P.card=4 ∧ P⊆D ∧
    (∀ p∈P,∀ q∈P,¬graph.Adj p q) ∧
    (∀ q∉D,∃ p∈P,graph.Adj q p) ∧
    (∀ q∉D,∀ p∈D,graph.Adj q p→p∈P) ∧
    ((8 : V)∉D) ∧
    (∀ q∉D,(D.filter (graph.Adj q)).card=1) := by decide

theorem outside_has_local_independence_four : localIndependence graph (8:V)=4 := by
  classical
  let N : Finset V := {0,9,10,11}
  have ne : ∀ x : V,x∈N ↔ graph.Adj 8 x := by decide
  have indep : ∀ x∈N,∀ y∈N,¬graph.Adj x y := by decide
  have cap : N.card=4 := by decide
  have m : N∈localIndependentSets graph 8 := by
    simp only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun x xm=>(ne x).mp xm,indep⟩
  unfold localIndependence
  rw [←cap]
  exact le_antisymm (Finset.sup_le_iff.mpr (fun S sm=>by
    have hs : (∀ x∈S,graph.Adj 8 x) ∧ (∀ x∈S,∀ y∈S,¬graph.Adj x y) := by
      simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and] using sm
    exact Finset.card_le_card (fun x xm=>(ne x).mpr (hs.1 x xm))))
    (Finset.le_sup (f:=Finset.card) m)

#print axioms four_free
#print axioms no_P9
#print axioms core_no_P7
#print axioms radius_eq_four
#print axioms four_isolated_ports
#print axioms outside_has_local_independence_four
end Graffiti133P5CliqueArms.FourIsolateFanBarrier
