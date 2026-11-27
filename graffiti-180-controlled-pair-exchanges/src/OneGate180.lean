import PairExchange180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Deleting a prescribed external vertex cannot seal a proper nonempty
region if another external vertex survives in the same biconnected graph. -/
theorem escape_gate (G : SimpleGraph V) (nc : NoCut G) (H : Finset V) (a z y : V)
    (ah : a∈H) (zh : z∉H) (yh : y∉H) (yz : y≠z) :
    ∃ i∈H,∃ j∉H,j≠z ∧ G.Adj i j := by
  classical
  by_contra no
  let S : Set V := {z}ᶜ
  let aa : S := ⟨a,show a≠z from fun e => zh (e ▸ ah)⟩
  let yy : S := ⟨y,yz⟩
  obtain ⟨p⟩ := nc z aa yy
  have push {s t : S} (q : (G.induce S).Walk s t) : s.val∈H → t.val∈H := by
    induction q with
    | nil => exact id
    | @cons i j k e _ ih =>
      intro h
      apply ih
      by_contra out
      exact no ⟨i.val,h,j.val,out,j.property,e⟩
  exact yh (push p ah)

/-- Every remote component with only one exit into the release set must
meet an old certificate vertex different from x. -/
theorem contact_of_one_gate (J : SimpleGraph V) (C Z : Finset V) (x y : V)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(univ\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (H : Finset V)
    (remoteH : H∈remote J ((univ\C)\Z) y)
    (gate : ∃ z∈Z, ∀ i∈H,∀ j∈Z,J.Adj i j → j=z) :
    ∃ b∈C.erase x,Dominates J H b := by
  classical
  let R := (univ\C)\Z
  let G := J⊔SimpleGraph.edge x y
  obtain ⟨hne,hm⟩ := mem_erase.mp remoteH
  obtain ⟨a,ar,ea⟩ := mem_image.mp hm
  have idH : part J R a=H := ea
  have mem {i : V} : i∈H ↔ i∈R ∧ (within J R).Reachable a i := by
    rw [←idH,mem_part]
  have yh : y∉H := fun h => hne (idH.symm.trans (part_eq_of_reach J R (mem.mp h).2))
  obtain ⟨z,hz,unique⟩ := gate
  have zy := (mem_erase.mp (zs hz)).1
  have zh : z∉H := fun h => (mem_sdiff.mp (mem.mp h).1).2 hz
  obtain ⟨i,ih,j,out,jz,edge⟩ := escape_gate G nc H a z y (mem.mpr ⟨ar,.refl _⟩) zh yh zy.symm
  have ir := (mem.mp ih).1
  have ix : i≠x := fun e => (mem_sdiff.mp (mem_sdiff.mp ir).1).2 (e ▸ tip.1)
  have iy : i≠y := fun e => yh (e ▸ ih)
  have old : J.Adj i j := by
    rcases edge with e|e
    · exact e
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact (ix h.1).elim
      · exact (iy h.1).elim
  have jx : j≠x := by
    intro e
    have ji : J.Adj x i := e ▸ old.symm
    exact tip.2.2.2.1 ⟨i,(mem_sdiff.mp ir).1,ji⟩
  have jc : j∈C := by
    by_contra outside
    have nz : j∉Z := fun h => jz (unique i ih j h old)
    have jr : j∈R := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,outside⟩,nz⟩
    have e : (within J R).Adj i j := ⟨old,ir,jr⟩
    exact out (mem.mpr ⟨jr,(mem.mp ih).2.trans e.reachable⟩)
  exact ⟨j,mem_erase.mpr ⟨jx,jc⟩,i,ih,old.symm⟩

/-- Biconnectivity supplies the return vertices, independently for the
surviving components. The returning set need not be specified in advance. -/
theorem first_of_saturated_gates (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y))
    (sat : ∀ b∈C.erase x,J.Adj x b)
    (feed : ∀ z∈Z,Dominates J ((univ\C)\Z) z)
    (budget : (remote J ((univ\C)\Z) y).card<Z.card)
    (gates : ∀ H∈remote J ((univ\C)\Z) y, ∃ z∈Z,∀ i∈H,∀ j∈Z,J.Adj i j → j=z) :
    FirstForm J U x y w := by
  classical
  let R := (univ\C)\Z
  have zs' : Z⊆(univ\C).erase y := by
    intro t h
    obtain ⟨ty,tc⟩ := mem_erase.mp (zs h)
    exact mem_erase.mpr ⟨ty,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp tc).2⟩⟩
  have empty : demand J R C Z x=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro q h
    obtain ⟨k,nr,nx⟩ := (mem_demand ..).mp h
    rcases mem_union.mp k with qc|qz
    · exact nx (sat q qc).symm
    · exact nr (feed q qz)
  apply first_of_requirement_budget J hc hn x y w xy old xw wy U C Z cu count tip zs
  · change (remote J R y).card+(demand J R C Z x).card<Z.card
    simpa only [empty,card_empty,Nat.add_zero] using budget
  · intro H h
    obtain ⟨b,bc,meet⟩ := contact_of_one_gate J C Z x y tip zs' nc H h (gates H h)
    exact ⟨b,bc,sat b bc,meet⟩
  · intro q h
    change q∈demand J R C Z x at h
    simp [empty] at h

#print axioms escape_gate
#print axioms contact_of_one_gate
#print axioms first_of_saturated_gates
end Minimal180.Controlled
