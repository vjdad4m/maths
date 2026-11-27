import IndependentBasis
import CographJoin

namespace Restrained534
open SimpleGraph Finset CographRadius
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def Restrained (D : Finset V) : Prop :=
  Dominates G D ∧ ∀ v, v ∉ D → ∃ w ∉ D, G.Adj v w

noncomputable def restrainedNumber : ℕ :=
  sInf {n : ℕ | ∃ D : Finset V, D.card = n ∧ Restrained G D}

theorem restrained_attained : ∃ D : Finset V, D.card = restrainedNumber G ∧ Restrained G D := by
  apply Nat.sInf_mem (s := {n : ℕ | ∃ D : Finset V, D.card = n ∧ Restrained G D})
  exact ⟨_,univ,rfl,fun v => Or.inl (mem_univ v),fun v h => (h (mem_univ v)).elim⟩

omit [Fintype V] in
theorem restrained_le {D : Finset V} (h : Restrained G D) : restrainedNumber G ≤ D.card :=
  Nat.sInf_le (s := {n : ℕ | ∃ S : Finset V, S.card = n ∧ Restrained G S}) ⟨D,rfl,h⟩

omit [Fintype V] in
private theorem dominating_nonempty [Nonempty V] {D : Finset V} (h : Dominates G D) :
    D.Nonempty := by
  let v : V := Classical.choice inferInstance
  rcases h v with hv|⟨w,hw,_⟩
  · exact ⟨v,hv⟩
  · exact ⟨w,hw⟩

omit [Fintype V] in
theorem two_le_of_no_universal [Nonempty V] (h : ¬ ∃ u, Universal G u)
    {D : Finset V} (hd : Dominates G D) : 2 ≤ D.card := by
  have pos := card_pos.mpr (dominating_nonempty G hd)
  by_contra! small
  obtain ⟨u,rfl⟩ := card_eq_one.mp (show D.card = 1 by omega)
  apply h
  refine ⟨u,fun v ne => ?_⟩
  rcases hd v with hv|⟨w,hw,adj⟩
  · exact (ne (mem_singleton.mp hv).symm).elim
  · simpa [mem_singleton.mp hw] using adj.symm

theorem independent_universal {u : V} (hu : Universal G u) : independentDomination G = 1 := by
  classical
  letI : Nonempty V := ⟨u⟩
  have dom : Dominates G {u} := by
    intro v
    by_cases h : v = u
    · exact Or.inl (mem_singleton.mpr h)
    · exact Or.inr ⟨u,mem_singleton_self u,(hu v (Ne.symm h)).symm⟩
  have ind : G.IsIndepSet (↑({u} : Finset V) : Set V) := by
    intro x hx y hy ne
    exact (ne ((mem_singleton.mp hx).trans (mem_singleton.mp hy).symm)).elim
  have upper : independentDomination G ≤ 1 :=
    Nat.sInf_le (s := {n : ℕ | ∃ D : Finset V, D.card = n ∧ G.IsIndepSet D ∧ Dominates G D})
      ⟨{u}, card_singleton u,ind,dom⟩
  obtain ⟨D,sz,_,hd⟩ := attained G
  have := card_pos.mpr (dominating_nonempty G hd)
  omega

/-- Vertices other than the center that become isolated when the center is deleted. -/
noncomputable def leavesAt (u : V) : Finset V := by
  classical
  exact univ.filter fun v => v ≠ u ∧ ∀ w, G.Adj v w → w = u

@[simp] theorem mem_leaves {u v : V} :
    v ∈ leavesAt G u ↔ v ≠ u ∧ ∀ w, G.Adj v w → w = u := by
  classical
  simp [leavesAt]

/-- Exact for every cone, including a star and the one-vertex graph. -/
theorem cone_formula {u : V} (hu : Universal G u) :
    restrainedNumber G = (leavesAt G u).card + 1 := by
  classical
  let L := leavesAt G u
  have center : u ∉ L := fun h => ((mem_leaves G).mp h).1 rfl
  have upper : Restrained G (insert u L) := by
    constructor
    · intro v
      by_cases h : v ∈ insert u L
      · exact Or.inl h
      · have ne : v ≠ u := fun e => h (mem_insert.mpr (Or.inl e))
        exact Or.inr ⟨u,mem_insert_self _ _,(hu v ne.symm).symm⟩
    · intro v hv
      have ne : v ≠ u := fun e => hv (mem_insert.mpr (Or.inl e))
      have hl : v ∉ L := fun h => hv (mem_insert_of_mem h)
      have second : ∃ w, G.Adj v w ∧ w ≠ u := by
        by_contra! none
        exact hl ((mem_leaves G).mpr ⟨ne,none⟩)
      obtain ⟨w,vw,wu⟩ := second
      exact ⟨w,fun h => (mem_insert.mp h).elim wu (fun hw =>
        ne (((mem_leaves G).mp hw).2 v vw.symm)),vw⟩
  obtain ⟨D,sz,hd,rest⟩ := restrained_attained G
  have sub : L ⊆ D := by
    intro v hv
    by_cases inside : v ∈ D
    · exact inside
    exfalso
    obtain ⟨w,hw,vw⟩ := (hd v).resolve_left inside
    obtain ⟨z,hz,vz⟩ := rest v inside
    have eq : w = z := (((mem_leaves G).mp hv).2 w vw).trans (((mem_leaves G).mp hv).2 z vz).symm
    exact hz (eq ▸ hw)
  have strict : L ≠ D := by
    rintro rfl
    obtain ⟨w,hw,uw⟩ := rest u center
    obtain ⟨z,hz,wz⟩ := (hd w).resolve_left hw
    exact uw.ne ((((mem_leaves G).mp hz).2 w wz.symm).symm)
  have lo := card_lt_card (ssubset_of_subset_of_ne sub strict)
  have hi := restrained_le G upper
  rw [card_insert_of_not_mem center] at hi
  change restrainedNumber G = L.card + 1
  omega

/-- A partition with both parts nonempty and every cross edge present. -/
def ProperJoin : Prop :=
  ∃ (A : V → Prop) (a b : V), A a ∧ ¬ A b ∧ ∀ u v, A u → ¬ A v → G.Adj u v

theorem cograph_join [Nontrivial V] (conn : G.Connected) (cog : Cograph G) : ProperJoin G := by
  let a : V := Classical.choice inferInstance
  obtain ⟨A,b,ha,hb,cross⟩ := join_at G conn cog a
  exact ⟨A,a,b,ha,hb,cross⟩

/-- A two-sided join without a universal vertex has a restrained dominating edge. -/
theorem nonuniversal_join [Nonempty V] (join : ProperJoin G)
    (no : ¬ ∃ u, Universal G u) : restrainedNumber G = 2 := by
  classical
  obtain ⟨A,a,b,ha,hb,cross⟩ := join
  have missing (v : V) : ∃ w, v ≠ w ∧ ¬ G.Adj v w := by
    by_contra! all
    exact no ⟨v,all⟩
  obtain ⟨a',aa',ma⟩ := missing a
  obtain ⟨b',bb',mb⟩ := missing b
  have ha' : A a' := by by_contra h; exact ma (cross a a' ha h)
  have hb' : ¬ A b' := fun h => mb (cross b' b h hb).symm
  have ab : a ≠ b := fun e => hb (e ▸ ha)
  let D : Finset V := {a,b}
  have outA : a' ∉ D := by simp [D,aa'.symm,show a' ≠ b from fun e => hb (e ▸ ha')]
  have outB : b' ∉ D := by simp [D,bb'.symm,show b' ≠ a from fun e => hb' (e.symm ▸ ha)]
  have valid : Restrained G D := by
    constructor
    · intro v
      by_cases h : A v
      · exact Or.inr ⟨b,by simp [D],cross v b h hb⟩
      · exact Or.inr ⟨a,by simp [D],(cross a v ha h).symm⟩
    · intro v _
      by_cases h : A v
      · exact ⟨b',outB,cross v b' h hb'⟩
      · exact ⟨a',outA,(cross a' v ha' h).symm⟩
  have hi := restrained_le G valid
  have sz : D.card = 2 := by simp [D,ab]
  obtain ⟨T,eqT,ht,_⟩ := restrained_attained G
  have lo := two_le_of_no_universal G no ht
  omega

theorem nonuniversal_cograph [Nontrivial V] (conn : G.Connected) (cog : Cograph G)
    (no : ¬ ∃ u, Universal G u) : restrainedNumber G = 2 :=
  nonuniversal_join G (cograph_join G conn cog) no

end Restrained534
