import HighEarFinish33

namespace Graffiti384b.HighEar
open Finset SimpleGraph EarAnchor EarOnClique33 CliquePivot33 EarExchange33
open private EarOnClique33.scarce_at_root from EarOnClique33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- If either cubic score is unavailable, at least one exterior neighbor of
each endpoint has at most one neighbor among the other exterior vertices. -/
theorem scarce_score_cap {e a c : V} (de : H.degree e=2) (da : 4≤H.degree a) (dc : 4≤H.degree c)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (lack : ¬Available H R) :
    additional H e a c=∅ ∧ trianglesAt H a≤2+(H.degree a-3).choose 2 := by
  classical
  obtain ⟨thin,x,xm,xa,xc,safe,_⟩ := thin_route H de da dc ea ec ac pos inj tight cl lack
  have apart := (scarce_cliques H lack de ac.ne ea ec pos inj tight cl).1
  obtain ⟨y,ym,_,bare⟩ := bare_neighbor H de da dc ea ec ac pos inj tight cl apart xm xa xc safe
  let D := exterior H e a c
  let S := D.erase y
  have sub : S⊆D := erase_subset ..
  have bound : S.filter (H.Adj y)⊆{x} := fun z m => mem_singleton.mpr
    (bare z (sub (mem_filter.mp m).1) (mem_filter.mp m).2)
  have one : nbr H y S≤1 := by simpa [nbr] using card_le_card bound
  have ear : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  obtain ⟨ds,score⟩ := exact_count H ear ea ec ac
  change D.card+2=H.degree a at ds
  change trianglesAt H a=1+(additional H e a c).card+(pairs H D).card at score
  have eq : insert y S = D := insert_erase ym
  have sum := pairs_insert H (D:=S) (not_mem_erase y D)
  rw [eq] at sum
  have ss : S.card=H.degree a-3 := by rw [show S=D.erase y from rfl,card_erase_of_mem (show y∈D from ym)]; omega
  have cap := card_filter_le (S.powersetCard 2) (fun p => ∀ i∈p,∀ j∈p,i≠j → H.Adj i j)
  change (pairs H S).card≤(S.powersetCard 2).card at cap
  rw [card_powersetCard,ss] at cap; rw [thin,card_empty] at score
  exact ⟨thin,by omega⟩

/-- A cubic leaf root in a failed attachment needs an endpoint of degree at
least six. A degree-five endpoint uses the other cubic score and makes that
root the only cubic in the core. -/
theorem cubic_root_profile {e a c r : V} (de : H.degree e=2) (dr : H.degree r=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (tight : Tight H {r}) {C : Finset V} (cl : H.IsNClique 5 C) :
    additional H e a c=∅ ∧ 5≤H.degree a ∧ 5≤H.degree c ∧ (6≤H.degree a ∨ 6≤H.degree c) ∧
    ((H.degree a=5 ∨ H.degree c=5) → ∀ v,H.degree v=3 → v=r) := by
  have lack := EarOnClique33.scarce_at_root H dr de pos inj
  obtain ⟨da,dc⟩ := CubicShore.endpoints H de ea ec ac pos inj half ⟨C,cl⟩
  obtain ⟨thin,ascore⟩ := scarce_score_cap H de da dc ea ec ac pos inj tight cl lack
  have cscore := (scarce_score_cap H de dc da ec ea ac.symm pos inj tight cl lack).2
  obtain ⟨a5,c5⟩ := endpoint_profile H de ea ec ac pos inj half ⟨C,cl⟩ (by rw [thin,card_empty]; decide)
  have low {v : V} (dv : 5≤H.degree v) : 2≤trianglesAt H v := by
    have diff : trianglesAt H v≠1 := by
      intro h; have eq := inj (h.trans (ear_one H de pos).symm); subst v; omega
    have := pos v; omega
  have high {v : V} (dv : H.degree v=5) (cap : trianglesAt H v≤2+(H.degree v-3).choose 2) :
      trianglesAt H v≤3 := by rw [dv] at cap; exact cap
  have asmall := fun h => high h ascore
  have csmall := fun h => high h cscore
  have rd := cubic_scores H de dr pos inj
  have uniq {w : V} (dw : 5≤H.degree w) (small : trianglesAt H w≤3) :
      ∀ v,H.degree v=3 → v=r := by
    intro v dv
    apply inj
    have vdiff : trianglesAt H v≠trianglesAt H w := by intro eq; have h := inj eq; subst v; omega
    have rdiff : trianglesAt H r≠trianglesAt H w := by intro eq; have h := inj eq; subst r; omega
    have := cubic_scores H de dv pos inj; have := low dw; omega
  have larger : 6≤H.degree a ∨ 6≤H.degree c := by
    by_contra! no
    have ha := asmall (by omega); have hc := csmall (by omega)
    have ad : trianglesAt H a≠trianglesAt H r := by intro eq; have h := inj eq; subst r; omega
    have cd : trianglesAt H c≠trianglesAt H r := by intro eq; have h := inj eq; subst r; omega
    have diff : trianglesAt H a≠trianglesAt H c := fun eq => ac.ne (inj eq)
    have := low a5; have := low c5; omega
  exact ⟨thin,a5,c5,larger,fun opt => opt.elim (fun h => uniq a5 (asmall h)) (fun h => uniq c5 (csmall h))⟩

/-- Two endpoints of degree at most five suffice for a cubic leaf attachment
in the order-33 case, regardless of their common neighbors. -/
theorem full_five_five (n : Fintype.card V=33) (t : (types H).card=33) {z b : V}
    (leaf : H.neighborFinset z={b}) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ r e a c : P,r.val=b → G.degree r=3 → G.degree e=2 → G.Adj e a → G.Adj e c →
    G.Adj a c → G.degree a≤5 → G.degree c≤5 → (∀ v,0<trianglesAt G v) →
    Function.Injective (trianglesAt G) → gamma G=16 → (∃ C,G.IsNClique 5 C) → gamma H=16 := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ r e a c : P,_
  intro r e a c rb dr de ea ec ac da dc pos inj g five
  obtain ⟨C,cl⟩ := five
  have ord : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have half : 2*gamma G=Fintype.card P := by change gamma G=16 at g; omega
  have sol : ∃ D,Exchange G r D := by
    apply (exchange_iff G r half).mp
    intro tight
    obtain ⟨_,_,_,large,_⟩ := cubic_root_profile G de dr ea ec ac pos inj half.ge tight cl
    change G.degree a≤5 at da
    change G.degree c≤5 at dc
    omega
  have up := (EarRoot33.attachment_iff H n t leaf r rb g).mpr sol
  change gamma G=16 at g
  have lo : gamma G≤gamma H := EarAnchorFinish.leaf_lower H leaf
  have cap : bound H=16 := by unfold bound; rw [t,n]
  omega

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.scarce_score_cap
#print axioms Graffiti384b.HighEar.cubic_root_profile
#print axioms Graffiti384b.HighEar.full_five_five
