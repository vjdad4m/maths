import ForceColor180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem forced_parity (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (D : Finset V) (r : V) (p : Bool) (inside : D⊆parity G r p) :
    parity (force G D) (.inl r) p=pull (forget D) (parity G r p) := by
  classical
  have bags := force_bags G D
  ext v
  cases v with
  | inl x =>
    have eq := bags.repDist gc (Sum.inl : V→Forced D) (fun _ => rfl) x r
    simp only [mem_parity,mem_pull,eq,forget,Sum.elim_inl,id_eq]
  | inr z =>
    have met := bags.metric gc hn (.inr z) (.inl r)
    change (force G D).dist (.inr z) (.inl r)=
      (if z.1.val≠r then G.dist z.1.val r else if (Sum.inr z:Forced D)=.inl r then 0 else if G.Adj z.1.val r then 1 else 2) at met
    by_cases eq : z.1.val=r
    · have rp : r∈parity G r p := eq ▸ inside z.1.property
      have pe : p=false := by cases p <;> simp_all [mem_parity,dist_self]
      simp [eq] at met
      simp [mem_parity,met,pe,eq,forget,dist_self]
    · simp [eq] at met
      simp [mem_parity,met,forget]

theorem full_pull_forget (D U : Finset V) : fullBags (forget D) (pull (forget D) U)=U := by
  ext i
  rw [full_iff]
  exact ⟨fun all => mem_pull.mp (all (.inl i) rfl),fun m x fx => mem_pull.mpr (fx ▸ m)⟩

theorem forced_eligible (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (D A : Finset V) (r : V) (p : Bool) (both : D⊆A∩parity G r p) :
    eligible (pull (forget D) A) (parity (force G D) (.inl r) p) (.inl r)=
      pull (forget D) (eligible A (parity G r p) r) := by
  classical
  rw [forced_parity G gc hn D r p (both.trans inter_subset_right)]
  ext x
  simp only [mem_pull,eligible_iff]
  cases x with
  | inl v => simp [forget]
  | inr z =>
    have az := (mem_inter.mp (both z.1.property)).1
    have pz := (mem_inter.mp (both z.1.property)).2
    by_cases eq : z.1.val=r
    · simp [forget,eq] at az pz ⊢
      simp [az,pz]
    · simp [forget,eq]

/-- Projecting a maximum bipartite witness from the independent-bag
expansion supplies a base witness containing the prescribed double marks
and paying their rooted inequality. Its base order is the order used here. -/
theorem forced_witness (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (A D : Finset V) (ai : Indep G A) (r : V) (p : Bool) (both : D⊆A∩parity G r p)
    (up : localBound (force G D) (.inl r) (parity (force G D) (.inl r) p)) :
    ∃ Z,TwoColor G Z ∧ D⊆Z ∧
      1+A.card+(parity G r p).card≤weightedLeaves G (eligible A (parity G r p) r)+Z.card := by
  classical
  let H := force G D
  let P := parity G r p
  let U := eligible A P r
  let f := forget D
  let m := Fintype.card (Copies D)
  have bags := force_bags G D
  have hc := bags.connected gc (by omega)
  have size := Fintype.card_le_of_surjective f bags.onto
  have pp := forced_parity G gc (by omega) D r p (both.trans inter_subset_right)
  have ue := forced_eligible G gc (by omega) D A r p both
  have upper := up _ (forced_indep G D A ai)
  rw [ue,pp] at upper
  have ac := pulled_size D A (both.trans inter_subset_left)
  have pc := pulled_size D P (both.trans inter_subset_right)
  have ui : D⊆U := by
    intro x xd
    have ab := mem_inter.mp (both xd)
    apply eligible_iff.mpr
    exact ⟨Or.inl ab.1,or_iff_not_imp_left.mpr (fun same => by rw [←not_not.mp same]; exact ab)⟩
  have uc := pulled_size D U ui
  have lf := bags.costLower hc (by omega) (pull f U)
  rw [full_pull_forget] at lf
  obtain ⟨W,col,opt⟩ := optB H
  have di : Indep G D := fun x xm y ym => ai x (both.trans inter_subset_left xm) y (both.trans inter_subset_left ym)
  obtain ⟨bc,inc,cap⟩ := forced_max G D di W col opt
  refine ⟨W.image f,bc,inc,?_⟩
  change 1+(pull f A).card+(pull f P).card≤weightedLeaves H (pull f U)+bipartiteNum H at upper
  change (pull f A).card=A.card+m at ac
  change (pull f P).card=P.card+m at pc
  change (pull f U).card=U.card+m at uc
  change weightedLeaves H (pull f U)+U.card≤(pull f U).card+weightedLeaves G U at lf
  change W.card≤(W.image f).card+m at cap
  change 1+A.card+P.card≤weightedLeaves G U+(W.image f).card
  omega

#print axioms forced_parity
#print axioms forced_eligible
#print axioms forced_witness
end Minimal180.Substitution
