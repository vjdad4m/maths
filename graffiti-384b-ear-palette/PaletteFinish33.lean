import PaletteSample33

namespace Graffiti384b.EarPalette
open Finset SimpleGraph EarAnchor HighEar
open private CubicShore.half_tight from CubicDiamondCut33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- With two additional common neighbors, any score four or five among
the four non-ear vertices supplies the missing score rank in the trial. -/
theorem shared_low {e a c s t : V} (n : Fintype.card V=32) (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (as' : H.Adj a s) (cs : H.Adj c s) (se : s≠e)
    (at' : H.Adj a t) (ct : H.Adj c t) (te : t≠e) (st : s≠t)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (low : ∃ w∈({a,c,s,t}:Finset V),trianglesAt H w=4 ∨ trianglesAt H w=5) :
    gamma H≤15 := by
  apply Nat.le_of_not_gt; intro bad
  have half : Fintype.card V≤2*gamma H := by omega
  have hit (C : Finset V) (cl : H.IsNClique 5 C) : a∈C ∨ c∈C :=
    hit_clique H de ea ec ac.ne as' cs se at' ct te st pos inj (CubicShore.half_tight H half) cl
  have ear : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  obtain ⟨w,wm,score⟩ := low
  have val := sampled_bound H n ear ea ec ac as' cs se at' ct te st score
    ⟨w,wm,rfl⟩ (ear_one H de pos) pos inj hit
  omega

/-- In a half-order core, the endpoints and every additional common neighbor
have at least six incident triangles as soon as there are two such neighbors. -/
theorem shared_scores_six {e a c s t : V} (n : Fintype.card V=32) (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (as' : H.Adj a s) (cs : H.Adj c s) (se : s≠e)
    (at' : H.Adj a t) (ct : H.Adj c t) (te : t≠e) (st : s≠t)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (five : ∃ C,H.IsNClique 5 C) (large : 16≤gamma H) :
    ∀ w∈({a,c,s,t}:Finset V),6≤trianglesAt H w := by
  have half : Fintype.card V≤2*gamma H := by omega
  have ls := CubicShore.square_profile H de ea ec ac pos inj half five as' cs se
  have lt := CubicShore.square_profile H de ea ec ac pos inj half five at' ct te
  intro w wm
  have four : 4≤trianglesAt H w := by
    rcases (show w=a ∨ w=c ∨ w=s ∨ w=t by simpa only [mem_insert,mem_singleton] using wm) with h|h|h|h
    · exact h ▸ (ls a (by simp)).1
    · exact h ▸ (ls c (by simp)).1
    · exact h ▸ (ls s (by simp)).1
    · exact h ▸ (lt t (by simp)).1
  apply Nat.le_of_not_gt; intro small
  have := shared_low H n de ea ec ac as' cs se at' ct te st pos inj ⟨w,wm,by omega⟩
  omega

/-- Every triangular ear with an endpoint of degree at most four in an
order-32 positive injective core containing a five-clique saves a vertex. -/
theorem core_le_fifteen {e a c : V} (n : Fintype.card V=32) (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (da : H.degree a≤4)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (five : ∃ C,H.IsNClique 5 C) : gamma H≤15 := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have half : Fintype.card V≤2*gamma H := by omega
  have lo := (CubicShore.endpoints H de ea ec ac pos inj half five).1
  have deg : H.degree a=4 := by omega
  obtain ⟨_,⟨s,t,st,ext⟩,opt⟩ := four_endpoint H de deg ea ec ac pos inj half five
  rcases opt with ⟨thin,_⟩|⟨eq,four⟩
  · have save := thin_four_below_half H de deg ea ec ac thin pos inj five; omega
  · have setEq : additional H e a c={s,t} := eq.trans ext
    obtain ⟨se,as',cs⟩ := (additional_mem H).mp (show s∈additional H e a c from setEq ▸ mem_insert_self ..)
    obtain ⟨te,at',ct⟩ := (additional_mem H).mp (show t∈additional H e a c from setEq ▸ mem_insert_of_mem (mem_singleton_self _))
    have val := shared_low H n de ea ec ac as' cs se at' ct te st.ne pos inj ⟨a,by simp,Or.inl four⟩
    omega

theorem extremal_endpoints {e a c : V} (n : Fintype.card V=32) (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (five : ∃ C,H.IsNClique 5 C) (half : 16≤gamma H) : 5≤H.degree a ∧ 5≤H.degree c := by
  constructor
  · apply Nat.le_of_not_gt; intro low
    have := core_le_fifteen H n de ea ec ac (by omega) pos inj five; omega
  · apply Nat.le_of_not_gt; intro low
    have := core_le_fifteen H n de ec ea ac.symm (by omega) pos inj five; omega

private theorem lift_small (n : Fintype.card V=33) (t : (types H).card=33) (z : V) :
    let P := ({z} : Finset V)ᶜ
    gamma (H.induce (P : Set V))≤15 → gamma H≤16 ∧ gamma H≤bound H := by
  let P := ({z} : Finset V)ᶜ
  change gamma (H.induce (P : Set V))≤15 → _
  intro save
  obtain ⟨X,cov,size⟩ := (gamma_induced_iff H (W:=P)).mp save
  have dom : TwoDominates H (insert z X) := by
    intro y out
    have yz : y≠z := fun eq => out (eq ▸ mem_insert_self ..)
    exact (cov.2 y (by simp [P,yz]) (fun m => out (mem_insert_of_mem m))).trans
      (Repair.nbr_mono H y (subset_insert ..))
  have up : gamma H≤(insert z X).card := Nat.sInf_le ⟨_,dom,rfl⟩
  have val : bound H=16 := by unfold Graffiti384b.bound; rw [n,t]
  have := card_insert_le z X
  exact ⟨by omega,by omega⟩

/-- At order and diversity 33, lifting the 15-vertex set works for every
position and every degree of the deleted vertex. -/
theorem full_bound (n : Fintype.card V=33) (t : (types H).card=33) (z : V) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ e a c : P,G.degree e=2 → G.Adj e a → G.Adj e c → G.Adj a c →
    (G.degree a≤4 ∨ G.degree c≤4) → (∀ v,0<trianglesAt G v) →
    Function.Injective (trianglesAt G) → (∃ C,G.IsNClique 5 C) →
    gamma G≤15 ∧ gamma H≤16 ∧ gamma H≤bound H := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ e a c : P,_
  intro e a c de ea ec ac small pos inj five
  have order : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have save : gamma G≤15 := small.elim (fun d => core_le_fifteen G order de ea ec ac d pos inj five)
    (fun d => core_le_fifteen G order de ec ea ac.symm d pos inj five)
  exact ⟨save,lift_small H n t z save⟩

/-- Full-graph lift of the score-four-or-five case for two shared neighbors.
The sampling branch does not require a five-clique existence assumption. -/
theorem full_shared (n : Fintype.card V=33) (t : (types H).card=33) (z : V) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ e a c s u : P,G.degree e=2 → G.Adj e a → G.Adj e c → G.Adj a c →
    G.Adj a s → G.Adj c s → s≠e → G.Adj a u → G.Adj c u → u≠e → s≠u →
    (∀ v,0<trianglesAt G v) → Function.Injective (trianglesAt G) →
    (∃ w∈({a,c,s,u}:Finset P),trianglesAt G w=4 ∨ trianglesAt G w=5) →
    gamma G≤15 ∧ gamma H≤16 ∧ gamma H≤bound H := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ e a c s u : P,_
  intro e a c s u de ea ec ac as' cs se au cu ue su pos inj low
  have order : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have save := shared_low G order de ea ec ac as' cs se au cu ue su pos inj low
  exact ⟨save,lift_small H n t z save⟩

end Graffiti384b.EarPalette
#print axioms Graffiti384b.EarPalette.shared_low
#print axioms Graffiti384b.EarPalette.shared_scores_six
#print axioms Graffiti384b.EarPalette.core_le_fifteen
#print axioms Graffiti384b.EarPalette.extremal_endpoints
#print axioms Graffiti384b.EarPalette.full_bound
#print axioms Graffiti384b.EarPalette.full_shared
