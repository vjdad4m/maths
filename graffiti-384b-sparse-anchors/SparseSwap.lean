import SparseMass
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph Simplicial16 TwoEars
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private FiniteRange.bad from FiniteRange384b
open private LowSample.anchor_samples from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem swap_mass (X E : Finset V) (sz : X.card=29) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    {e v z b : V} (em : e∈E) (vm : v∈X) (zm : z∈X) (bm : b∈X)
    (vb : v≠b) (zb : z≠b) (vz : v≠z) (eb : G.Adj e b) (ev : G.Adj e v)
    (sc : trianglesAt G v=2) (dg : G.degree v=3) (guard : Protects G v {e,z})
    (free : nbr G v (E.erase e)=0)
    (failure : Fintype.card V<gamma G+16) :
    3124550+3*(29:ℕ).choose (11)+(∑ v∈E,(29-nbr G v X).choose (11-nbr G v X))+(∑ v∈X,((X.powersetCard (11)).filter (fun s => v∈activated G X s)).card)+(∑ v∈X,((X.powersetCard (11)).filter (fun s => v∈extra G X E s)).card)≤
      ∑ v∈X,((X.powersetCard (11)).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard (11)
  have kc : K.card=(29:ℕ).choose (11) := by dsimp [K]; rw [card_powersetCard,sz]
  let favorable (s : Finset V) := v∈s ∧ z∈s ∧ b∉s
  have each (s : Finset V) (sm : s∈K) :
      (if favorable s then 1 else 0)+(3+(Joint17.eligible G X E s).card+(activated G X s).card+
      (extra G X E s).card)≤(FiniteRange.bad G X s).card := by
    obtain ⟨sub,ks⟩ := mem_powersetCard.mp sm
    by_cases fs : favorable s
    · obtain ⟨vs,zs,bs⟩ := fs
      let F := E.erase e
      have trial := extra_trial G X F s (sep.mono_right (erase_subset ..))
        (fun u um w wm => ind u (mem_erase.mp um).2 w (mem_erase.mp wm).2)
        (fun u um => two u (mem_erase.mp um).2) sub hx inj
      have elig : Joint17.eligible G X F s=Joint17.eligible G X E s := by
        ext u; constructor
        · intro um; obtain ⟨hu,h⟩ := mem_filter.mp um; exact mem_filter.mpr ⟨(mem_erase.mp hu).2,h⟩
        · intro um; obtain ⟨hu,h⟩ := mem_filter.mp um
          refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_,hu⟩,h⟩
          rintro rfl; exact bs (h (mem_filter.mpr ⟨bm,eb⟩))
      have zero {i : V} (h : nbr G i E=0) : nbr G i F=0 :=
        Nat.eq_zero_of_le_zero ((card_le_card (filter_subset_filter _ (erase_subset ..))).trans h.le)
      have add : insert v (extra G X E s)⊆extra G X F s := by
        refine insert_subset ?_ ?_
        · refine mem_filter.mpr ⟨vs,sc,dg,free,{e,z},guard,insert_subset ?_ (singleton_subset_iff.mpr (mem_union_right _ zs))⟩
          exact mem_union_left _ (mem_compl.mpr (fun ex => disjoint_left.mp sep ex em))
        · intro i im; obtain ⟨is,score,deg,off,rest⟩ := mem_filter.mp im
          exact mem_filter.mpr ⟨is,score,deg,zero off,rest⟩
      have ne : v∉extra G X E s := by
        intro h; have vanish := (mem_filter.mp h).2.2.2.1
        have non := card_pos.mpr (show (E.filter (G.Adj v)).Nonempty from ⟨e,mem_filter.mpr ⟨em,ev.symm⟩⟩)
        change 0<nbr G v E at non; omega
      have gain := card_le_card add
      rw [card_insert_of_not_mem ne] at gain
      rw [elig,card_sdiff sub,sz,ks] at trial
      rw [if_pos (show favorable s from ⟨vs,zs,bs⟩)]; omega
    · have trial := extra_trial G X E s sep ind two sub hx inj
      rw [card_sdiff sub,sz,ks] at trial; rw [if_neg fs]; omega
  have events : 3124550≤(K.filter favorable).card := by
    let Y := X.erase b
    have inc : ({v,z}:Finset V)⊆Y := insert_subset (mem_erase.mpr ⟨vb,vm⟩)
      (singleton_subset_iff.mpr (mem_erase.mpr ⟨zb,zm⟩))
    have ct := LowSample.anchor_samples Y {v,z} 11 inc (by rw [card_pair vz]; decide)
    rw [show Y.card=28 from by dsimp [Y]; rw [card_erase_of_mem bm,sz],card_pair vz] at ct
    apply (show 3124550≤(28-2:ℕ).choose (11-2) by decide).trans (ct.trans (card_le_card ?_))
    intro s sm
    obtain ⟨sel,inside⟩ := mem_filter.mp sm
    obtain ⟨sy,sz'⟩ := mem_powersetCard.mp sel
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sy.trans (erase_subset ..),sz'⟩,inside (mem_insert_self ..),
      inside (mem_insert_of_mem (mem_singleton_self _)),fun bs => (mem_erase.mp (sy bs)).1 rfl⟩
  have z := sum_le_sum each
  simp only [sum_add_distrib,sum_boole,sum_const,smul_eq_mul,kc] at z
  have cnt : (∑ s∈K,if favorable s then 1 else 0)=(K.filter favorable).card := by
    simpa using (sum_filter (s:=K) (p:=favorable) (f:=fun _ => (1:ℕ))).symm
  rw [cnt] at z
  have flip (P : Finset V) (F : Finset V → Finset V) (sub : ∀ s∈K,F s⊆P) :
      (∑ s∈K,(F s).card)=∑ v∈P,(K.filter (fun s => v∈F s)).card := by
    calc _ = ∑ s∈K,∑ v∈P,if v∈F s then 1 else 0 := by
             apply sum_congr rfl; intro s sm; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub s sm)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  rw [flip X (extra G X E) (fun s sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1),flip X (activated G X) (fun s sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1),flip E (Joint17.eligible G X E) (fun _ _ => filter_subset ..),flip X (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset)] at z
  have fiber (v : V) (vm : v∈E) : (29-nbr G v X).choose (11-nbr G v X)≤(K.filter (fun s => v∈Joint17.eligible G X E s)).card := by
    have small : (Joint17.poolNbr G X v).card≤2 := by
      rw [←two v vm,←card_neighborFinset_eq_degree]
      exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    have lim := LowSample.anchor_samples X (Joint17.poolNbr G X v) (11) (filter_subset ..) (by omega)
    rw [sz] at lim
    simpa [K,Joint17.eligible,vm,Joint17.poolNbr,nbr] using lim
  have gain := sum_le_sum fiber
  change 3124550+3*(29:ℕ).choose (11)+(∑ v∈E,(29-nbr G v X).choose (11-nbr G v X))+(∑ v∈X,(K.filter (fun s => v∈activated G X s)).card)+(∑ v∈X,(K.filter (fun s => v∈extra G X E s)).card)≤∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card
  rw [Nat.mul_comm ((29:ℕ).choose (11)) 3] at z
  omega
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.swap_mass
