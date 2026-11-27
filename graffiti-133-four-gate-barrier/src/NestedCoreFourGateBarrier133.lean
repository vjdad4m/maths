import NestedCoreThreeGate133

namespace Graffiti133NestedCore.FourGateBarrier
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

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

def E : List (Fin 12×Fin 12) := [(4,6),(6,7),(7,5),(4,8),(8,9),(9,5),
  (4,10),(10,11),(11,5),(0,4),(0,5),(1,6),(2,7),(2,8),(3,9),(3,10),(1,11)]

def adjB (x y : Fin 12) : Bool := decide ((x,y)∈E ∨ (y,x)∈E)

def graph : SimpleGraph (Fin 12) where
  Adj x y := adjB x y=true
  symm := by
    intro x y h
    have q : (x,y)∈E ∨ (y,x)∈E := of_decide_eq_true h
    exact decide_eq_true q.symm
  loopless := by
    change ∀ x : Fin 12, ¬ adjB x x=true
    decide

instance : DecidableRel graph.Adj := fun x y => inferInstanceAs (Decidable (adjB x y=true))

def base : Finset (Fin 12) := {0,1,2,3}

def color (x : Fin 12) : Fin 12 := ([0,0,0,0,0,0,1,2,2,3,3,1] : List (Fin 12)).getD x.val 0

theorem exact_single_gate : ∀ x : Fin 12,x∉base →
    color x∈base ∧ ∀ y∈base,graph.Adj x y ↔ y=color x := by decide

theorem four_free : FourCycleFree graph := by
  have h : ∀ a b : Fin 12,a≠b→
      ((Finset.univ : Finset (Fin 12)).filter fun x=>graph.Adj a x ∧ graph.Adj b x).card≤1 := by decide
  intro a b x y ab ax bx ay byy
  exact Finset.card_le_one.mp (h a b ab) x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ax,bx⟩)
    y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ay,byy⟩)

set_option maxRecDepth 100000 in
theorem no_P9 : ¬∃ f : Fin 9→Fin 12,InducedPath graph f := by
  have b : (List.finRange 12).any (fun x=>dfs adjB 8 x [])=false := by decide
  rintro ⟨f,h⟩
  have d := dfs_complete adjB (fun _ _=>Iff.rfl) f h (0:Fin 9) 8 (by decide) [] (by simp)
  have t : (List.finRange 12).any (fun x=>dfs adjB 8 x [])=true :=
    List.any_eq_true.mpr ⟨f 0,List.mem_finRange _,d⟩
  rw [b] at t
  contradiction

set_option maxRecDepth 100000 in
theorem exact_gain_two :
    (∑ w : Fin 12,localIndependence graph w)+4*base.card=
      (∑ w : (base : Set (Fin 12)),localIndependence (graph.induce (base : Set (Fin 12))) w)+
        4*Fintype.card (Fin 12)+2 := by
  have ambient := sum_degree_eq_local_add_triangles four_free
  have core := sum_degree_eq_local_add_triangles (Graffiti133MultiWeighted.restricted_c4 four_free base)
  have et : graph.edgeFinset.card=17 := by decide
  have tf : graph.CliqueFree 3 := by
    have finite : ∀ a b c : Fin 12,graph.Adj a b→ graph.Adj a c→ ¬graph.Adj b c := by decide
    intro S hs
    obtain ⟨a,b,c,ab,ac,bc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact finite a b c ab ac bc
  have tt (d : DecidableEq (Fin 12)) (a : DecidableRel graph.Adj) :
      @triangleCount (Fin 12) _ d graph a=0 := by
    letI : DecidableEq (Fin 12) := d
    letI : DecidableRel graph.Adj := a
    change (graph.cliqueFinset 3).card=0
    rw [tf.cliqueFinset,Finset.card_empty]
  have ec : (graph.induce (base : Set (Fin 12))).edgeFinset.card=0 := by decide
  have nc : base.card=4 := by decide
  have n : Fintype.card (Fin 12)=12 := by decide
  rw [ec] at core
  rw [et,tt] at ambient
  omega

#print axioms exact_gain_two
#print axioms exact_single_gate
#print axioms four_free
#print axioms no_P9
end Graffiti133NestedCore.FourGateBarrier
