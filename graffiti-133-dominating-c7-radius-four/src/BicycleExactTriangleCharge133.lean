import Mathlib.Combinatorics.SimpleGraph.Clique
import BicycleOneExteriorTriangle133

namespace Graffiti133ExteriorSlack
open SimpleGraph Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V]

theorem minimal_positive_slack_one (n t s : Nat)
    (hn : 3≤n) (ht : 2≤t) (hs : 0<s)
    (combined : n*s + 3*t ≤ 2*s + 2*n) : s=1 := by
  by_contra! evil
  have s2 : 2≤s := by omega
  let q := s-2
  have sq : s=q+2 := by dsimp [q]; omega
  have qn : 3*q≤n*q := Nat.mul_le_mul_right _ hn
  rw [sq,Nat.mul_add] at combined
  omega

theorem finite_minimal_slack_profile (e t s : Nat) (r d : V→Nat)
    (hn : 3≤Fintype.card V) (ht : 2≤t) (hs : 0<s)
    (excess : 2*e=2*Fintype.card V+3*t+s)
    (degree_sum : (∑ v : V,d v)=2*e)
    (triangle_sum : (∑ v : V,r v)=3*t)
    (perVertex : ∀ v, s+3*r v+2≤2*d v) :
    s=1 ∧ t%2=1 ∧
      (∀ v, 2+r v+(r v/2)≤d v) ∧
      (∑ v : V,(d v-(2+r v)))=1 ∧
      (∑ v : V,r v/2)≤1 := by
  have sumL := Finset.sum_le_sum (s:=Finset.univ) (fun v _=>perVertex v)
  have ls : (∑ v : V,(s+3*r v+2))=Fintype.card V*s+9*t+2*Fintype.card V := by
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,triangle_sum]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change Fintype.card V*s+3*(3*t)+Fintype.card V*2= _
    omega
  have rs : (∑ v : V,2*d v)=4*e := by rw [←Finset.mul_sum,degree_sum]; omega
  rw [ls,rs] at sumL
  have rel : Fintype.card V*s+3*t≤2*s+2*Fintype.card V := by omega
  have one : s=1 := minimal_positive_slack_one _ _ _ hn ht hs rel
  have odd : t%2=1 := by omega
  have bound (v : V) : 2+r v+r v/2≤d v := by
    have h := perVertex v
    omega
  have nonneg (v : V) : 2+r v≤d v := by have := bound v; omega
  have combined : (∑ v : V,(d v-(2+r v))) + (2*Fintype.card V+3*t)=2*e := by
    calc
      _ = ∑ v : V,((d v-(2+r v))+(2+r v)) := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib,triangle_sum]
        simp [Nat.mul_comm]
      _ = ∑ v : V,d v := Finset.sum_congr rfl (fun v _=>Nat.sub_add_cancel (nonneg v))
      _ = 2*e := degree_sum
  have surplus : (∑ v : V,(d v-(2+r v)))=1 := by omega
  have nums : (∑ v : V,r v/2) ≤ ∑ v : V,(d v-(2+r v)) := by
    apply Finset.sum_le_sum
    intro v _
    have := bound v
    omega
  exact ⟨one,odd,bound,surplus,by omega⟩

theorem unique_spare_profile (g : V→Nat) (sumOne : (∑ v : V,g v)=1) :
    ∃ u, g u=1 ∧ ∀ v≠u,g v=0 := by
  classical
  obtain ⟨u,hu⟩ : ∃ u,0<g u := by
    by_contra! no
    have z : (∑ v : V,g v)=0 := Finset.sum_eq_zero (fun v _=>by have := no v; omega)
    omega
  have u1 : g u=1 := by
    have one := Finset.single_le_sum (s:=Finset.univ) (fun v _=>Nat.zero_le (g v)) (Finset.mem_univ u)
    omega
  refine ⟨u,u1,?_⟩
  intro v vu
  have both : (∑ k∈({u,v}:Finset V),g k) ≤ ∑ k : V,g k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
  have eq : (∑ k∈({u,v}:Finset V),g k)=g u+g v := by simp [vu.symm]
  rw [eq] at both
  omega

theorem tight_degree_profile (r d : V→Nat)
    (bound : ∀ v,2+r v+r v/2≤d v)
    (surplus : (∑ v : V,(d v-(2+r v)))=1) :
    ∃ u, (d u=3+r u ∧ r u≤3) ∧ ∀ v≠u,(d v=2+r v ∧ r v≤1) := by
  obtain ⟨u,hu,hv⟩ := unique_spare_profile (fun v=>d v-(2+r v)) surplus
  refine ⟨u,?_,?_⟩
  · have h := bound u
    change d u-(2+r u)=1 at hu
    omega
  · intro v ne
    have h := bound v
    have z := hv v ne
    change d v-(2+r v)=0 at z
    omega

#print axioms finite_minimal_slack_profile
#print axioms tight_degree_profile
end Graffiti133ExteriorSlack


namespace Graffiti133ExteriorSlack
open SimpleGraph Finset Graffiti133Bicycle Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def triangleCount : Nat := (G.cliqueFinset 3).card

def triangleIncidence (v : V) : Nat := ((G.cliqueFinset 3).filter fun S=>v∈S).card

theorem sum_incidence : (∑ v : V,triangleIncidence G v)=3*triangleCount G := by
  classical
  unfold triangleIncidence triangleCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have one (T : Finset V) (hT : T∈G.cliqueFinset 3) :
      (∑ v : V, (if v∈T then (1:Nat) else 0))=3 := by
    rw [←Finset.card_filter]
    have eq : (Finset.univ.filter fun v=>v∈T)=T := by ext; simp
    rw [eq]
    exact (SimpleGraph.mem_cliqueFinset_iff.mp hT).card_eq
  rw [Finset.sum_congr rfl one]
  simp [Nat.mul_comm]

private def subtypeEmb (x : V) : {y : V // y≠x} ↪ V :=
  ⟨Subtype.val,Subtype.val_injective⟩

private theorem clique_delete_map (x : V) (T : Finset {y : V // y≠x}) :
    (G.induce {y : V | y≠x}).IsNClique 3 T ↔ G.IsNClique 3 (T.map (subtypeEmb x)) := by
  rw [SimpleGraph.isNClique_iff,SimpleGraph.isNClique_iff,Finset.card_map]
  refine and_congr_left' ?_
  constructor
  · intro h a am b bm ne
    obtain ⟨u,um,eq⟩ := Finset.mem_map.mp am
    obtain ⟨v,vm,hv⟩ := Finset.mem_map.mp bm
    change u.val=a at eq
    change v.val=b at hv
    subst a
    subst b
    exact h um vm (fun e=>ne (congrArg Subtype.val e))
  · intro h a am b bm ne
    exact h (Finset.mem_map.mpr ⟨a,am,rfl⟩) (Finset.mem_map.mpr ⟨b,bm,rfl⟩)
      (fun e=>ne (Subtype.ext e))

theorem triangle_count_deletion (x : V) :
    triangleCount (G.induce {y : V | y≠x})+triangleIncidence G x=triangleCount G := by
  classical
  have count : ((G.induce {y : V | y≠x}).cliqueFinset 3).card =
      ((G.cliqueFinset 3).filter fun T=>x∉T).card := by
    apply Finset.card_bij (fun T _=>T.map (subtypeEmb x))
    · intro T hT
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_cliqueFinset_iff).mpr ((clique_delete_map G x T).mp
        (SimpleGraph.mem_cliqueFinset_iff.mp hT)),?_⟩
      intro hx
      obtain ⟨a,_,e⟩ := Finset.mem_map.mp hx
      exact a.property e
    · intro a _ b _ eq
      exact Finset.map_injective _ eq
    · intro T hT
      obtain ⟨keep,hx⟩ := Finset.mem_filter.mp hT
      let Q := T.subtype (fun y=>y≠x)
      have map : Q.map (subtypeEmb x)=T := by
        ext y
        constructor
        · intro hy
          obtain ⟨z,zm,e⟩ := Finset.mem_map.mp hy
          change z.val=y at e
          exact e ▸ (Finset.mem_subtype.mp zm)
        · intro hy
          have yx : y≠x := fun e=>hx (e ▸ hy)
          exact Finset.mem_map.mpr ⟨⟨y,yx⟩,Finset.mem_subtype.mpr hy,rfl⟩
      refine ⟨Q,(SimpleGraph.mem_cliqueFinset_iff).mpr ((clique_delete_map G x Q).mpr ?_),map⟩
      rw [map]
      exact (G.mem_cliqueFinset_iff).mp keep
  unfold triangleCount triangleIncidence
  rw [count,Nat.add_comm]
  exact Finset.filter_card_add_filter_neg_card_eq_card _

private theorem delete_vertex_card (x : V) : Fintype.card {y : V // y≠x}+1=Fintype.card V := by
  rw [Fintype.card_subtype,Finset.filter_ne']
  exact (Finset.card_erase_add_one (Finset.mem_univ x)).trans Finset.card_univ

theorem deleted_charge_upper (x : V)
    (bound : 2 * (G.induce {y : V | y≠x}).edgeFinset.card ≤
      2*Fintype.card {y : V // y≠x} + 3*triangleCount (G.induce {y : V | y≠x}))
    (s : Nat) (slack : 2*G.edgeFinset.card=2*Fintype.card V+3*triangleCount G+s) :
    s+3*triangleIncidence G x+2≤2*G.degree x := by
  have e := card_delete_add_degree G x
  have n := delete_vertex_card x
  have t := triangle_count_deletion G x
  omega

theorem graph_minimal_slack_profile
    (hn : 3≤Fintype.card V) (ht : 2≤triangleCount G) (s : Nat) (hs : 0<s)
    (slack : 2*G.edgeFinset.card=2*Fintype.card V+3*triangleCount G+s)
    (minimal : ∀ x : V, 2 * (G.induce {y : V | y≠x}).edgeFinset.card ≤
      2*Fintype.card {y : V // y≠x} + 3*triangleCount (G.induce {y : V | y≠x})) :
    s=1 ∧ triangleCount G % 2=1 ∧
      ∃ u, (G.degree u=3+triangleIncidence G u ∧ triangleIncidence G u≤3) ∧
        ∀ v≠u,(G.degree v=2+triangleIncidence G v ∧ triangleIncidence G v≤1) := by
  obtain ⟨one,odd,bound,spare,_⟩ := finite_minimal_slack_profile G.edgeFinset.card
    (triangleCount G) s (triangleIncidence G) (fun v => G.degree v) hn ht hs slack
    G.sum_degrees_eq_twice_card_edges (sum_incidence G) (fun x=>deleted_charge_upper G x (minimal x) s slack)
  exact ⟨one,odd,tight_degree_profile _ _ bound spare⟩

#print axioms triangle_count_deletion
#print axioms graph_minimal_slack_profile
end Graffiti133ExteriorSlack


namespace Graffiti133OuterCore
open SimpleGraph Graffiti133 Finset
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

noncomputable def neighborhood (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

theorem mem_neighborhood {v x : V} : x∈neighborhood G v ↔ G.Adj v x := by
  classical
  simp [neighborhood]

noncomputable def triangleTips (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  let N := neighborhood G v
  exact N.filter (fun x => ∃ y∈N, G.Adj x y ∧ y<x)

theorem localIndependence_add_triangleTips (h4 : FourCycleFree G) (v : V) :
    localIndependence G v + (triangleTips G v).card = (neighborhood G v).card := by
  classical
  let N := neighborhood G v
  let D := triangleTips G v
  have Dsub : D⊆N := fun _ h => (Finset.mem_filter.mp h).1
  have only {x a b : V} (hx : x∈N) (ha : a∈N) (hb : b∈N)
      (ha' : G.Adj x a) (hb' : G.Adj x b) : a=b :=
    h4 v x a b (mem_neighborhood.mp hx).ne
      (mem_neighborhood.mp ha) ha' (mem_neighborhood.mp hb) hb'
  have existsPartner (a : V) (ha : a∈D) : ∃ b∈N, G.Adj a b ∧ b<a :=
    (Finset.mem_filter.mp ha).2
  let mate (a : V) := if h : a∈D then Classical.choose (existsPartner a h) else a
  have mates {a : V} (ha : a∈D) : mate a∈N ∧ G.Adj a (mate a) ∧ mate a<a := by
    simpa only [mate,dif_pos ha] using Classical.choose_spec (existsPartner a ha)
  obtain ⟨A,hA,maxA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  have aProp := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have Asub : A⊆N := fun a h => mem_neighborhood.mpr (aProp.1 a h)
  let pick (a : V) := if a∈A then mate a else a
  have conflict {a b : V} (ha : a∈D) (hb : b∈D) (eq : a=mate b) : False := by
    have ma := mates ha
    have mb := mates hb
    have eq' : mate a=b := only (Dsub ha) ma.1 (Dsub hb) ma.2.1
      (by rw [eq]; exact mb.2.1.symm)
    rw [eq'] at ma
    exact (not_lt_of_gt (eq ▸ mb.2.2)) ma.2.2
  have drop : D.card ≤ (N \ A).card := by
    apply Finset.card_le_card_of_injOn pick
    · intro a ha
      by_cases ain : a∈A
      · have ma := mates ha
        have n : mate a∉A := fun q => aProp.2 a ain (mate a) q ma.2.1
        simpa [pick,ain] using (Finset.mem_sdiff.mpr ⟨ma.1,n⟩ : mate a∈N\A)
      · simpa [pick,ain] using (Finset.mem_sdiff.mpr ⟨Dsub ha,ain⟩ : a∈N\A)
    · intro a ha b hb eq
      by_cases ai : a∈A <;> by_cases bi : b∈A
      · have both : mate a=mate b := by simpa [pick,ai,bi] using eq
        exact only (mates ha).1 (Dsub ha) (Dsub hb) (mates ha).2.1.symm
          (both.symm ▸ (mates hb).2.1.symm)
      · have w : b=mate a := (show mate a=b by simpa [pick,ai,bi] using eq).symm
        exact (conflict hb ha w).elim
      · have w : a=mate b := by simpa [pick,ai,bi] using eq
        exact (conflict ha hb w).elim
      · simpa [pick,ai,bi] using eq
  let B := N\D
  have bm : B∈localIndependentSets G v := by
    apply Graffiti133Pentagon.PentagonFrame.memLocalSet.mpr
    refine ⟨fun x h => mem_neighborhood.mp (Finset.mem_sdiff.mp h).1,?_⟩
    intro x hx y hy e
    rcases lt_or_gt_of_ne e.ne with h|h
    · exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy).1,x,(Finset.mem_sdiff.mp hx).1,e.symm,h⟩)
    · exact (Finset.mem_sdiff.mp hx).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1,y,(Finset.mem_sdiff.mp hy).1,e,h⟩)
  have below : B.card≤localIndependence G v := Finset.le_sup (f:=Finset.card) bm
  change (N\D).card≤localIndependence G v at below
  have cardB := Finset.card_sdiff_add_card_eq_card Dsub
  have cardA := Finset.card_sdiff_add_card_eq_card Asub
  change localIndependence G v + D.card=N.card
  omega

#print axioms localIndependence_add_triangleTips
end Graffiti133OuterCore


namespace Graffiti133ExactTriangleCharge
open SimpleGraph Finset Graffiti133 Graffiti133OuterCore Graffiti133ExteriorSlack
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

private theorem pair_around_clique (v : V) (T : Finset V) (hT : G.IsNClique 3 T) (vm : v∈T) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b ∧ b<a ∧ T={v,a,b} := by
  obtain ⟨a,b,c,ab,ac,bc,e⟩ := SimpleGraph.is3Clique_iff.mp hT
  rw [e] at vm
  simp only [Finset.mem_insert,Finset.mem_singleton] at vm
  have ordered (x y z : V) (xy : G.Adj x y) (xz : G.Adj x z) (yz : G.Adj y z)
      (e' : T=({x,y,z}:Finset V)) :
      ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b ∧ b<a ∧ T={x,a,b} := by
    rcases lt_or_gt_of_ne yz.ne with lt|gt
    · refine ⟨z,y,xz,xy,yz.symm,lt,?_⟩
      rw [e']
      ext k
      simp [or_comm,or_left_comm]
    · exact ⟨y,z,xy,xz,yz,gt,e'⟩
  rcases vm with va|vb|vc <;> subst v
  · exact ordered a b c ab ac bc e
  · exact ordered b a c ab.symm bc ac (by rw [e]; ext x; simp [or_comm,or_left_comm])
  · exact ordered c a b ac.symm bc.symm ab (by rw [e]; ext x; simp [or_comm,or_left_comm])

private theorem mem_tip (v x : V) : x∈triangleTips G v ↔
    x∈neighborhood G v ∧ ∃ y∈neighborhood G v,G.Adj x y ∧ y<x := by
  letI : DecidableRel G.Adj := Classical.decRel _
  exact Finset.mem_filter

theorem tips_card_is_incidence (h4 : FourCycleFree G) (v : V) :
    (triangleTips G v).card=triangleIncidence G v := by
  classical
  unfold triangleIncidence
  symm
  let F := (G.cliqueFinset 3).filter (fun T=>v∈T)
  have param (T : Finset V) (hT : T∈F) :
      ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b ∧ b<a ∧ T={v,a,b} :=
    pair_around_clique v T (SimpleGraph.mem_cliqueFinset_iff.mp (Finset.mem_filter.mp hT).1)
      (Finset.mem_filter.mp hT).2
  choose head tail hs using param
  change F.card=(triangleTips G v).card
  apply Finset.card_bij head
  · intro T hT
    obtain ⟨va,vb,ab,lt,e⟩ := hs T hT
    exact (mem_tip v _).mpr ⟨mem_neighborhood.mpr va,tail T hT,mem_neighborhood.mpr vb,ab,lt⟩
  · intro A am B bm eq
    obtain ⟨va,va',a,_,ea⟩ := hs A am
    obtain ⟨vb,vb',b,_,eb⟩ := hs B bm
    have aux : tail A am=tail B bm := h4 v (head A am) _ _ va.ne va' a vb'
      (by rw [eq]; exact b)
    rw [ea,eb,eq,aux]
  · intro a am
    obtain ⟨va,b,vb,ab,lt⟩ := (mem_tip v a).mp am
    have ea := mem_neighborhood.mp va
    have eb := mem_neighborhood.mp vb
    let T : Finset V := {v,a,b}
    have tm : T∈F := Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr (SimpleGraph.is3Clique_triple_iff.mpr ⟨ea,eb,ab⟩),by simp [T]⟩
    refine ⟨T,tm,?_⟩
    obtain ⟨h1,h2,_,less,same⟩ := hs T tm
    have hm : head T tm∈T := Eq.mpr (congrArg (fun A=>head T tm∈A) same) (by simp)
    have lm : tail T tm∈T := Eq.mpr (congrArg (fun A=>tail T tm∈A) same) (by simp)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hm lm
    rcases hm with hv|ha|hb
    · exact (h1.ne hv.symm).elim
    · exact ha
    · rcases lm with lv|la|lb
      · exact (h2.ne lv.symm).elim
      · rw [hb,la] at less
        exact (not_lt_of_gt lt less).elim
      · rw [hb,lb] at less
        exact (lt_irrefl _ less).elim

theorem sum_degree_eq_local_add_triangles (h4 : FourCycleFree G) :
    (∑ v : V,localIndependence G v)+3*triangleCount G=2*G.edgeFinset.card := by
  have point (v : V) : localIndependence G v+triangleIncidence G v=G.degree v := by
    rw [←tips_card_is_incidence h4]
    have q := localIndependence_add_triangleTips h4 v
    have e : neighborhood G v=G.neighborFinset v := by
      ext w
      rw [mem_neighborhood,G.mem_neighborFinset]
    simpa [e,G.card_neighborFinset_eq_degree] using q
  have sum := Finset.sum_congr rfl (fun v (_ : v ∈ (Finset.univ : Finset V))=>point v)
  rw [Finset.sum_add_distrib,sum_incidence,G.sum_degrees_eq_twice_card_edges] at sum
  exact sum

#print axioms sum_degree_eq_local_add_triangles
end Graffiti133ExactTriangleCharge
