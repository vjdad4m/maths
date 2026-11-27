import HighEarDetour33

namespace Graffiti384b.HighEar
open Finset SimpleGraph OneEar EarAnchor EarFrame33 CliquePivot33
open private HighEar.outside_cubic from HighEarPins33
open private CubicShore.half_tight from CubicDiamondCut33
open private EarAnchor.sees_in_clique from CubicAnchor33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A thin triangular ear with a degree-four endpoint gives a strict
improvement over half the order in the positive injective core. -/
theorem thin_four_below_half {e a c : V} (de : H.degree e=2) (da : H.degree a=4)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (thin : additional H e a c=∅)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (five : ∃ C,H.IsNClique 5 C) : 2*gamma H<Fintype.card V := by
  classical
  apply Nat.lt_of_not_ge; intro half
  obtain ⟨C,cl⟩ := five
  obtain ⟨s,t,u,st,D,sc,tc,anc,cnc,du,ns,only⟩ := four_layout H de da ea ec ac thin pos inj half cl
  have N : H.neighborFinset u=C\{s,t} := by rw [ns,D]
  have dc := (CubicShore.endpoints H de ea ec ac pos inj half ⟨C,cl⟩).2
  obtain ⟨m,q,big,par,first,second,qu,qC⟩ := triangle_detour H de da.ge dc ea ec ac st D pos inj half cl sc tc anc cnc du N only
  let U := H.neighborFinset u
  have us : U.card=3 := (card_neighborFinset_eq_degree ..).trans du
  have subC : U⊆C := by change H.neighborFinset u⊆C; rw [N]; exact sdiff_subset
  have uC : u∉C := fun h => by have := EarAnchor.sees_in_clique H cl h; omega
  have en : e∉C := fun h => by have := EarAnchor.sees_in_clique H cl h; omega
  have neith {v} (vm:v∈U) : v≠s ∧ v≠t := by
    have vv : v∈C\{s,t} := N ▸ vm
    simpa [not_or] using (mem_sdiff.mp vv).2
  have avoidU {z} (zm:z∈U) (i) (hi : i≤m) : q.atIdx i≠z := by
    intro eq
    have cm : q.atIdx i∈C := eq ▸ subC zm
    exact (qC i hi cm).elim (fun h => (neith zm).1 (eq.symm.trans h)) (fun h => (neith zm).2 (eq.symm.trans h))
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<U.card by omega)
  let L := U.erase x
  have ls : L.card=2 := by rw [show L=U.erase x from rfl,card_erase_of_mem xm,us]
  have lu : L⊆U := erase_subset ..
  obtain ⟨P,Q,fr,eb,xp,xq,_,_,at0,at1,miss⟩ := cycle_pins H (K:=∅) (by simp)
    (show x≠e from fun eq => en (eq ▸ subC xm)) big par q.atIdx q.step q.unique q.avoid (avoidU xm)
    (by rw [q.start]; exact ea) (by rw [q.finish]; exact ec) (by simp)
  have sp : s∈P := second ▸ at0 2 (by omega) (by decide)
  have tq : t∈Q := first ▸ at1 1 (by omega) (by decide)
  have offU (z) (zm:z∈U) : z∉P∪Q := miss z (fun eq => en (eq ▸ subC zm)) (avoidU zm)
  have umiss := miss u (fun eq => by subst u; omega) qu
  let A := insert u P
  let B := Q∪L
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro y ya yb
    rcases mem_insert.mp ya with rfl|yp <;> rcases mem_union.mp yb with yq|yl
    · exact umiss (mem_union_right _ yq)
    · exact uC (subC (lu yl))
    · exact disjoint_left.mp fr.1 yp yq
    · exact offU y (lu yl) (mem_union_left _ yp)
  have sa : s∈A := mem_insert_of_mem sp
  have ua : u∈A := mem_insert_self ..
  have tb : t∈B := mem_union_left _ tq
  have su : s≠u := fun eq => uC (eq ▸ sc)
  have sees {z} (zm:z∈U) : 2≤nbr H z A := PinnedColor34.two H su
    (cl.1 (subC zm) sc (neith zm).1) ((H.mem_neighborFinset _ _).mp zm).symm sa ua
  have frame : Frame H A B := by
    refine ⟨dis,?_,?_⟩
    · intro y ym
      rcases mem_insert.mp ym with eqy|yp
      · subst y
        have eq : L.filter (H.Adj u)=L := filter_true_of_mem (fun z zm => (H.mem_neighborFinset _ _).mp (lu zm))
        exact (show 2≤nbr H u L by simp [nbr,eq,ls]).trans (Repair.nbr_mono H u subset_union_right)
      · exact (fr.2.1 y yp).trans (Repair.nbr_mono H y subset_union_left)
    · intro y ym
      rcases mem_union.mp ym with yq|yl
      · exact (fr.2.2 y yq).trans (Repair.nbr_mono H y (subset_insert ..))
      · exact sees (lu yl)
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<L.card by omega)
  have xy := (mem_erase.mp ym).1.symm
  have xb : 2≤nbr H x B := PinnedColor34.two H (neith (lu ym)).2.symm
    (cl.1 (subC xm) tc (neith xm).2) (cl.1 (subC xm) (subC (lu ym)) xy) tb (mem_union_right _ ym)
  have xinA : x∉A := fun h => (mem_insert.mp h).elim (fun eq => uC (eq ▸ subC xm)) xp
  have xinB : x∉B := fun h => (mem_union.mp h).elim xq (not_mem_erase x U)
  obtain ⟨z,za,_,_,dz,_⟩ := HighEar.outside_cubic H de pos inj (mem_union_left _ eb) (CubicShore.half_tight H half)
    frame xinA xinB (sees xm) xb
  exact za (only z dz ▸ ua)

/-- Except at exactly two additional common neighbors, both endpoints
in a half-order obstruction have degree at least five. -/
theorem endpoint_profile {e a c : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) (five : ∃ C,H.IsNClique 5 C)
    (count : (additional H e a c).card≠2) : 5≤H.degree a ∧ 5≤H.degree c := by
  have high {u v : V} (eu : H.Adj e u) (ev : H.Adj e v) (uv : H.Adj u v)
      (cap : (additional H e u v).card≠2) : 5≤H.degree u := by
    have lo := (CubicShore.endpoints H de eu ev uv pos inj half five).1
    by_cases d : H.degree u=4
    · obtain ⟨two,_,opt⟩ := four_endpoint H de d eu ev uv pos inj half five
      rcases opt with h|h
      · have := thin_four_below_half H de d eu ev uv h.1 pos inj five; omega
      · exact (cap (h.1 ▸ two)).elim
    · omega
  exact ⟨high ea ec ac count,high ec ea ac.symm (by simpa [additional,inter_comm] using count)⟩

/-- Lift the strict saving to the precise order-33 catalogue inequality. -/
theorem full_thin_four (n : Fintype.card V=33) (t : (types H).card=33) (z : V) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ e a c : P,G.degree e=2 → G.degree a=4 → G.Adj e a → G.Adj e c → G.Adj a c →
    additional G e a c=∅ → (∀ v,0<trianglesAt G v) → Function.Injective (trianglesAt G) →
    (∃ C,G.IsNClique 5 C) → gamma G≤15 ∧ gamma H≤bound H := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ e a c : P,_
  intro e a c de da ea ec ac thin pos inj five
  have order : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have save := thin_four_below_half G de da ea ec ac thin pos inj five
  change 2*gamma G<Fintype.card P at save
  have small : gamma G≤15 := by omega
  refine ⟨small,?_⟩
  obtain ⟨X,cov,size⟩ := (gamma_induced_iff H (W:=P)).mp small
  have dom : TwoDominates H (insert z X) := by
    intro y out
    have yz : y≠z := fun eq => out (eq ▸ mem_insert_self ..)
    exact (cov.2 y (by simp [P,yz]) (fun m => out (mem_insert_of_mem m))).trans
      (Repair.nbr_mono H y (subset_insert ..))
  have up : gamma H≤(insert z X).card := Nat.sInf_le ⟨_,dom,rfl⟩
  have val : bound H=16 := by unfold Graffiti384b.bound; rw [n,t]
  have := card_insert_le z X
  omega

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.thin_four_below_half
#print axioms Graffiti384b.HighEar.endpoint_profile
#print axioms Graffiti384b.HighEar.full_thin_four
