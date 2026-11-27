import HighEarPins33

namespace Graffiti384b.HighEar
open Finset SimpleGraph EarAnchor CliquePivot33 EarOnClique33 EarExchange33
open private Repair.triangles_le_choose from Repair384b
open private CubicShore.half_tight from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem cubic_scores {e u : V} (de : H.degree e=2) (du : H.degree u=3)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) :
    trianglesAt H u=2 ∨ trianglesAt H u=3 := by
  have diff : trianglesAt H u≠1 := by
    intro eq
    have ue := inj (eq.trans (ear_one H de pos).symm)
    subst u; omega
  have cap := Repair.triangles_le_choose H u; rw [du] at cap
  have hi : trianglesAt H u≤3 := cap
  have := pos u; omega

private theorem unique_other {e u : V} (de : H.degree e=2) (du : H.degree u=3)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {s t : V} (su : s≠u) (tu : t≠u) (ds : H.degree s=3) (dt : H.degree t=3) : s=t := by
  apply inj
  have cs := cubic_scores H de ds pos inj
  have ct := cubic_scores H de dt pos inj
  have cu := cubic_scores H de du pos inj
  have notS : trianglesAt H s≠trianglesAt H u := fun q => su (inj q)
  have notT : trianglesAt H t≠trianglesAt H u := fun q => tu (inj q)
  omega

/-- If exactly the opposite endpoint and the second common neighbor are in
the five-clique, its other three vertices are covered by uncredited cubics.
No single cubic, even a credited one, is adjacent to all three. -/
theorem triple {e a c w : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (an : a∉C) (cc : c∈C) (wc : w∈C) :
    let K := C\{c,w}
    (∀ x∈K,∃ u,u∉R ∧ H.degree u=3 ∧ H.Adj u x) ∧
    ∀ u,H.degree u=3 → ¬K⊆H.neighborFinset u := by
  classical
  let K := C\{c,w}
  have ks : K.card=3 := by
    rw [show K=C\{c,w} from rfl,card_sdiff (insert_subset cc (singleton_subset_iff.mpr wc)),cl.2,card_pair cw.ne]
  constructor
  · intro x xm
    obtain ⟨mx,off⟩ := mem_sdiff.mp xm
    obtain ⟨xc,xw⟩ := (show x≠c ∧ x≠w by simpa [not_or] using off)
    exact first_pins H de ea ec aw cw we.symm ac.ne pos inj tight cl an cc wc mx xc xw
  · intro u du sub
    have dsize : (H.neighborFinset u).card=3 := (card_neighborFinset_eq_degree ..).trans du
    have eq : H.neighborFinset u=K := (eq_of_subset_of_card_le sub (by change (H.neighborFinset u).card≤K.card; omega)).symm
    obtain ⟨x,xm⟩ := card_pos.mp (show 0<K.card by omega)
    have forced (y : V) (ym : y∈K) := second_pins H de du ea ec ac aw cw we.symm pos inj tight cl an cc wc eq (sub ym)
    obtain ⟨v,vu,_,dv,_⟩ := forced x xm
    have subV : K⊆H.neighborFinset v := by
      intro y ym
      obtain ⟨t,tu,_,dt,ty⟩ := forced y ym
      exact (H.mem_neighborFinset _ _).mpr (unique_other H de du pos inj tu vu dt dv ▸ ty)
    have eqV : K=H.neighborFinset v := eq_of_subset_of_card_le subV (by rw [ks,card_neighborFinset_eq_degree,dv])
    apply vu; apply inj; unfold trianglesAt; rw [eq,eqV]

private theorem both_of_triple {K R : Finset V} {e : V} (de : H.degree e=2)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) (kn : K.Nonempty)
    (cover : ∀ x∈K,∃ u,u∉R ∧ H.degree u=3 ∧ H.Adj u x)
    (holes : ∀ u,H.degree u=3 → ¬K⊆H.neighborFinset u) : Available H R := by
  obtain ⟨x,xm⟩ := kn
  obtain ⟨u,ur,du,_⟩ := cover x xm
  obtain ⟨y,ym,miss⟩ := not_subset.mp (holes u du)
  obtain ⟨v,vr,dv,vy⟩ := cover y ym
  have ne : v≠u := fun eq => miss ((H.mem_neighborFinset _ _).mpr (eq ▸ vy))
  have diff : trianglesAt H v≠trianglesAt H u := fun h => ne (inj h)
  rcases cubic_scores H de du pos inj with us|us
  · exact ⟨u,v,du,us,ur,dv,by have := cubic_scores H de dv pos inj; omega,vr⟩
  · exact ⟨v,u,dv,by have := cubic_scores H de dv pos inj; omega,vr,du,us,ur⟩

/-- Just one common neighbor in addition to the ear forces both cubic scores
away from every credited vertex. This allows any set R of vertices carrying one credit each. -/
theorem shared_requires_both {e a c w : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (aw : H.Adj a w) (cw : H.Adj c w) (we : w≠e)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) : Available H R := by
  classical
  apply Classical.byContradiction; intro missing
  obtain ⟨notBoth,allW⟩ := scarce_cliques H missing de ac.ne ea ec pos inj tight cl
  obtain ⟨wc,inside⟩ := allW w we aw cw
  have use {p q : V} (off : p∉C) (onC : q∈C) (ep : H.Adj e p) (eq : H.Adj e q)
      (pq : H.Adj p q) (pw : H.Adj p w) (qw : H.Adj q w) : Available H R := by
    obtain ⟨cover,holes⟩ := triple H de ep eq pq pw qw we pos inj tight cl off onC wc
    have size : (C\{q,w}).card=3 := by
      rw [card_sdiff (insert_subset onC (singleton_subset_iff.mpr wc)),cl.2,card_pair qw.ne]
    exact both_of_triple H de pos inj (card_pos.mp (by omega)) cover holes
  apply missing
  rcases inside with am|cm
  · exact use (fun cm => notBoth ⟨am,cm⟩) am ec ea ac.symm cw aw
  · exact use (fun am => notBoth ⟨am,cm⟩) cm ea ec ac aw cw

/-- A leaf at any cubic core vertex satisfies the order-33 catalogue bound
when the edge between the ear endpoints belongs to a second triangle. -/
theorem cubic_attachment (n : Fintype.card V=33) (t : (types H).card=33) {z b : V}
    (leaf : H.neighborFinset z={b}) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ r e a c w : P,r.val=b → G.degree r=3 → G.degree e=2 → G.Adj e a → G.Adj e c →
      G.Adj a c → G.Adj a w → G.Adj c w → w≠e → (∀ v,0<trianglesAt G v) →
      Function.Injective (trianglesAt G) → gamma G=16 → (∃ C,G.IsNClique 5 C) → gamma H=16 := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ r e a c w : P,_
  intro r e a c w rb dr de ea ec ac aw cw we pos inj g five
  obtain ⟨C,cl⟩ := five
  have ord : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have half : 2*gamma G=Fintype.card P := by change gamma G=16 at g; omega
  have sol : ∃ D,Exchange G r D := by
    apply (exchange_iff G r half).mp
    intro tight
    obtain ⟨u,v,_,us,ur,_,vs,vr⟩ := shared_requires_both G de ea ec ac aw cw we pos inj tight cl
    rcases cubic_scores G de dr pos inj with s|s
    · exact ur (mem_singleton.mpr (inj (us.trans s.symm)))
    · exact vr (mem_singleton.mpr (inj (vs.trans s.symm)))
  have up := (EarRoot33.attachment_iff H n t leaf r rb g).mpr sol
  change gamma G=16 at g
  have lo : gamma G≤gamma H := EarAnchorFinish.leaf_lower H leaf
  have cap : bound H=16 := by unfold bound; rw [t,n]
  omega

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.triple
#print axioms Graffiti384b.HighEar.shared_requires_both
#print axioms Graffiti384b.HighEar.cubic_attachment
