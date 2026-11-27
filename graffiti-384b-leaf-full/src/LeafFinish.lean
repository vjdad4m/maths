import LeafSample
namespace Graffiti384b.LeafPath
open Finset SimpleGraph Simplicial16
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A three-ear independent family with one ear supported entirely outside
a 28-vertex high pool forces the catalogue saving. -/
theorem safe_ear (n : Fintype.card V=33) (X E : Finset V) (sz : X.card=28)
    (fs : E.card=3) (sep : Disjoint X E) (hx : X⊆high G)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    {e : V} (em : e∈E) (safe : nbr G e X=0) : gamma G≤17 := by
  by_contra! fail
  let gain := fun v => (28-nbr G v X).choose (11-nbr G v X)
  have m := mass G X E sz sep ind two hx inj n fail
  have r := ranked G X sz hx inj lo
  change 2*(28:ℕ).choose 11+(∑ v∈E,gain v)+_≤_ at m
  have ec : gain e=21474180 := by dsimp [gain]; rw [safe,Nat.choose_eq_fast_choose]; decide
  have low (v : V) (vm : v∈E.erase e) : 3124550≤gain v := by
    have bound := card_le_card (show X.filter (G.Adj v)⊆G.neighborFinset v from fun _ w => (G.mem_neighborFinset ..).mpr (mem_filter.mp w).2)
    rw [card_neighborFinset_eq_degree,two v (mem_erase.mp vm).2] at bound
    change nbr G v X≤2 at bound
    have num : ∀ j : Fin 3,3124550≤(28-j.val).choose (11-j.val) := by simp only [Nat.choose_eq_fast_choose]; decide
    exact num ⟨nbr G v X,by omega⟩
  have sum := sum_le_sum low
  rw [sum_const,card_erase_of_mem em,fs] at sum
  have split := sum_erase_add E gain em
  rw [ec] at split
  rw [show (28:ℕ).choose 11=21474180 by rw [Nat.choose_eq_fast_choose]; decide] at m
  norm_num at sum
  omega

/-- The leaf-adjacent independent-ear branch satisfies the catalogue bound.
There is no assumption about common neighbors of different ears. -/
theorem exact_leaf (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    {e l : V} (de : G.degree e=2) (dl : G.degree l=1) (el : G.Adj e l) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨hs,es⟩ := Cover31.residual G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  let N := G.neighborFinset e
  have lm : l∈N := (G.mem_neighborFinset ..).mpr el
  have lc : (N.erase l).card=1 := by rw [card_erase_of_mem lm]; change G.degree e-1=1; omega
  have small : high G∩N⊆N.erase l := by
    intro w wm
    obtain ⟨wh,wn⟩ := mem_inter.mp wm
    apply mem_erase.mpr; refine ⟨?_,wn⟩; rintro rfl
    have hi := (mem_filter.mp wh).2
    omega
  have cap := (card_le_card small).trans lc.le
  have split := card_sdiff_add_card_inter (high G) N
  obtain ⟨X,sub,sz⟩ := exists_subset_card_eq (show 28≤((high G)\N).card by omega)
  let E := LowSample.twos G
  have two (v : V) (vm : v∈E) : G.degree v=2 := by
    obtain ⟨nl,nh⟩ := mem_sdiff.mp vm
    have a := (mem_filter.mp nl).2
    have b : ¬3≤G.degree v := fun z => nh (mem_filter.mpr ⟨mem_univ _,z⟩)
    omega
  have em : e∈E := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun m => by have a := (mem_filter.mp m).2; omega⟩
  have hx : X⊆high G := sub.trans sdiff_subset
  have sep : Disjoint X E := disjoint_left.mpr (fun _ wm ve => (mem_sdiff.mp ve).2 (hx wm))
  have safe : nbr G e X=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro w wm
    exact (mem_sdiff.mp (sub (mem_filter.mp wm).1)).2 ((G.mem_neighborFinset ..).mpr (mem_filter.mp wm).2)))
  have upper := safe_ear G n X E sz es sep hx (fun u um v vm => ind u v (two u um) (two v vm)) two
    (inj.mono (show (X:Set V)⊆high G from hx)) (fun v vm => floor v (hx vm)) em safe
  rw [bound,n,t] at bad; omega

/-- Consequently every independent-ear failure has a pair of ears with
a unique shared neighbor, and every ear neighbor has degree at least three. -/
theorem remaining (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v) (bad : bound G<gamma G) :
    (∀ u v,G.degree u=2 → G.Adj u v → 3≤G.degree v) ∧
      ∃ u v w,u≠v ∧ G.degree u=2 ∧ G.degree v=2 ∧ G.neighborFinset u∩G.neighborFinset v={w} := by
  have no {u v : V} (du : G.degree u=2) (dv : G.degree v=1) (uv : G.Adj u v) : False :=
    (not_lt_of_ge (exact_leaf G n q t ind du dv uv)) bad
  refine ⟨?_,(Clean.leaf_or_shared G n q t ind bad).resolve_left (by rintro ⟨u,v,du,dv,uv⟩; exact no du dv uv)⟩
  intro u v du uv
  have one : G.degree v≠1 := fun h => no du h uv
  have two : G.degree v≠2 := fun h => ind u v du h uv
  have pos : 0<(G.neighborFinset v).card := card_pos.mpr ⟨u,(G.mem_neighborFinset ..).mpr uv.symm⟩
  rw [card_neighborFinset_eq_degree] at pos; omega

end Graffiti384b.LeafPath
#print axioms Graffiti384b.LeafPath.safe_ear
#print axioms Graffiti384b.LeafPath.exact_leaf
#print axioms Graffiti384b.LeafPath.remaining
