import OffFiveConnectedTwinTable189
import OffFiveConnectedTwinGraphCompat189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data pin_pos LeftMarks RightMarks no_endpoints same_support_optimal reverse_long reverse_pin from SmallOrderFour189
open private length_ten_two_pin_shape pins_gap_at_four from FourOffGraphSupport189
open private off_five_pin_set_eq from OffFiveMixedClose189
open private hamilton_of_labeled_chain from FourOffGraphCore189
open private off_five_disconnected_single_marks off_five_single_pre_forward off_five_single_pre_exact model_d2_cap_any from DisconnectedSingleGraphVerified
open private path_neighbor_is_pin_of_off from OffFiveMixedMarks189
open private two_pin_flanks_path_only two_pin_universal_in_omitted_component from FourOffGraphSupport189
open private two_pins_choose_ordered left_boundary_porters_at_most_two right_boundary_porters_at_most_two from FourOffGraphCore189
open private off_five_tail_four off_five_tail_relabel off_five_tail_relabel_tail off_five_tail_relabel_low off_five_tail_relabel_inj from DisconnectedSingleGraphVerified

open private off_five_connected_twin_mask off_five_connected_twin_mask_canonical from OffFiveConnectedTwinGraphShape189
open private off_five_connected_twin_forward off_five_connected_twin_exact_core off_five_connected_twin_exact_ends from OffFiveConnectedTwinGraphCompat189
open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_degree_cap
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (φ : Fin 16→V) (inj : Function.Injective φ) (sur : Function.Surjective φ)
    (j : ℕ) (m : Marks) (C : Codes) (M : List Bool)
    (fw : ∀ u v,edge j m C M u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u : Fin 16,11≤u.val → ∀ v,G.Adj (φ u) (φ v) → edge j m C M u v=true) :
    degreeCap j m C M := by
  classical
  have exactDegree (u : Fin 16) (uh : 11≤u.val) : deg j m C M u=G.degree (φ u) := by
    let N := (univ : Finset (Fin 16)).filter (fun v => edge j m C M u v=true)
    have eq : N.image φ=G.neighborFinset (φ u) := by
      ext v
      constructor
      · intro h
        obtain ⟨k,km,rfl⟩ := mem_image.mp h
        exact (mem_neighborFinset G (φ u) _).mpr (fw _ _ (mem_filter.mp km).2)
      · intro h
        obtain ⟨k,rfl⟩ := sur v
        exact mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,rev u uh k ((mem_neighborFinset G (φ u) _).mp h)⟩,rfl⟩
    have c := congrArg Finset.card eq
    rw [card_image_of_injective _ inj,card_neighborFinset_eq_degree] at c
    exact c
  unfold degreeCap
  by_contra! too
  obtain ⟨u,um,v,vm,ne⟩ := one_lt_card.mp too
  obtain ⟨_,ul,ud⟩ := mem_filter.mp um
  obtain ⟨_,vl,vd⟩ := mem_filter.mp vm
  have dh := degree (φ u) (φ v) (fun e => ne (inj e))
  rw [←exactDegree u ul,←exactDegree v vl] at dh
  omega

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_oriented
    (table : ∀ {j : ℕ} {m : Marks},OffFive16DisconnectedSingle.candidate j m=true →
        row j (List.ofFn m)=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (hx : x∈H.vertices) (whole : ∀ v∉p.support,v∈H.vertices)
    {j : ℕ} (jlo : 4≤j) (xPins : Pins p x=({1,j}:Finset ℕ)) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have x1 : 1∈Pins p x := by rw [xPins]; simp
  have xj : j∈Pins p x := by rw [xPins]; simp
  have jl := (pin_data xj).1
  have jhi : j≤9 := by omega
  have xo := H.off x hx
  have holes := (length_ten_two_pin_shape hc even conn degree hp ah bh len xo x1 xj (by omega)).2.2
  obtain ⟨m,m0,m9,hm,nz,valid,L,R⟩ :=
    off_five_disconnected_single_marks hp.1 ah bh len xo x1 xj jlo holes
  obtain ⟨φ,C,inj,sur,at11,value,inside,gc,portModel⟩ :=
    off_five_connected_twin_labeling hc even hp.1 ah bh len off H hx whole x1 xj
  obtain ⟨ports,universals⟩ := connected_double_porter_shape hc even conn degree hp ah bh H hx x1 xj (by omega)
  let ψ : Fin 12→V := fun k => φ (Fin.castLE (by decide : 12≤16) k)
  have inj12 : Function.Injective ψ := by
    intro u v h
    exact Fin.ext (congrArg (fun z : Fin 16 => z.val) (inj h))
  have val12 (k : Fin 12) (kl : k.val≤10) : ψ k=p.getVert k.val :=
    value (Fin.castLE (by decide : 12≤16) k) kl
  have x12 : ψ 11=x := at11
  have fw := off_five_single_pre_forward len jhi ψ val12 x12 x1 xj m L R
  obtain ⟨E0,E10,E11⟩ := off_five_single_pre_exact hp.1 len j ψ val12 x12 xo xPins m L R
  have cap12 (z : Fin 12) (e : ∀ v,G.Adj (ψ z) (ψ v) → OffFive16DisconnectedSingle.edge j m z v=true) :
      (OffFive16DisconnectedSingle.two j m z).card≤4 :=
    model_d2_cap_any hc even (OffFive16DisconnectedSingle.edge j m) ψ inj12 fw z e
  have signs := OffFive16DisconnectedSingle.strictly_reduce_marks j m m0 m9 hm nz valid
    (cap12 0 E0) (cap12 10 E10) (cap12 11 E11)
    (fun n => OffFive16DisconnectedSingle.allPreMixed j jlo (by omega))
    OffFive16DisconnectedSingle.allBoundary
  let M := off_five_connected_twin_mask G φ C
  have ml : M.length=6 := by simp [M,off_five_connected_twin_mask,tailPairs]
  have cm : canonical C M=true := off_five_connected_twin_mask_canonical φ C
  have offH (k : Fin 16) (kl : 11≤k.val) : φ k∉p.support := H.off _ (inside k kl)
  have portSub (k : Fin 16) (kl : 11≤k.val) : Pins p (φ k)⊆({1,j}:Finset ℕ) := ports _ (inside k kl)
  have dbl (k : Fin 16) (kl : 11≤k.val) (h : code C k.val=3) : 2≤(Pins p (φ k)).card := by
    have p1 := (portModel k kl).1.mp (.inr h)
    have pj := (portModel k kl).2.mp (.inr h)
    have sub : ({1,j}:Finset ℕ)⊆Pins p (φ k) := by
      intro q qm
      have e : q=1 ∨ q=j := by simpa using qm
      rcases e with rfl|rfl <;> assumption
    have c := card_le_card sub
    simpa [show 1≠j by omega] using c
  have UC (u v : Fin 16) (ul : 11≤u.val) (vl : 11≤v.val) (ne : u≠v)
      (one : code C u.val=3 ∨ code C v.val=3) : G.Adj (φ u) (φ v) := by
    have dne : φ u≠φ v := fun e => ne (inj e)
    rcases one with one|one
    · exact universals _ (inside u ul) (dbl u ul one) _ (inside v vl) dne.symm
    · exact (universals _ (inside v vl) (dbl v vl one) _ (inside u ul) dne).symm
  have FW := off_five_connected_twin_forward φ value j jhi m C portModel UC fw
  have ER := off_five_connected_twin_exact_core hp.1 len φ value offH j m C portModel portSub UC E11
  have cap16 (z : Fin 16) (e : ∀ v,G.Adj (φ z) (φ v) → edge j m C M z v=true) : (two j m C M z).card≤4 :=
    model_d2_cap_any hc even (edge j m C M) φ inj FW z e
  have DC : caps j m C M two := ⟨
    cap16 0 (off_five_connected_twin_exact_ends hp.1 len φ value offH j m C 0 (.inl rfl) E0),
    cap16 10 (off_five_connected_twin_exact_ends hp.1 len φ value offH j m C 10 (.inr rfl) E10),
    cap16 11 (ER 11 (by decide)),cap16 12 (ER 12 (by decide)),cap16 13 (ER 13 (by decide)),
    cap16 14 (ER 14 (by decide)),cap16 15 (ER 15 (by decide))⟩
  have gd : degreeCap j m C M := off_five_connected_twin_degree_cap degree φ inj sur j m C M FW ER
  obtain ⟨l,span⟩ := span_from_row (table signs) gc ml cm gd DC
  letI : Nonempty V := ⟨a⟩
  exact hamilton_of_labeled_chain φ inj sur l span.1 span.2.1 (span.2.2.imp FW)

#print axioms off_five_connected_twin_oriented

/-- Five omitted vertices, an arbitrary connected omitted component covering them
all, and a double porter: this branch is traceable given the finite sign rows. -/
theorem traceable_if_five_off_connected_twin_with_table
    (table : ∀ {j : ℕ} {m : OffFive16ConnectedTwin.Marks},
      OffFive16DisconnectedSingle.candidate j m=true →
        OffFive16ConnectedTwin.row j (List.ofFn m)=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (hx : x∈H.vertices)
    (whole : ∀ v∉p.support,v∈H.vertices)
    (xTwo : 2≤(Pins p x).card) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have cap := fun v => distanceTwo_le_of_even 4 v (even v)
  have few {a b : V} {q : G.Walk a b} (opt : EdgeOptimal q)
      (z : V) (zo : z∉q.support) : (Pins q z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree opt zo).1
  have xo := H.off x hx
  obtain ⟨i,j,xi,xj,ij⟩ := two_pins_choose_ordered xTwo
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo xi xj ij
  have ilo := pin_pos hp.1 xo xi
  have shape := (length_ten_two_pin_shape hc even conn degree hp ah bh len xo xi xj ij).1
  rcases shape with rfl|rfl
  · exact off_five_connected_twin_oriented table hc even conn degree hp ah bh len off H hx whole
      (by omega) (off_five_pin_set_eq (few hp x xo) xi xj (by omega))
  have rev : EdgeOptimal p.reverse :=
    same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have rlen : p.reverse.length=10 := by simpa using len
  have roff : ((univ : Finset V)\p.reverse.support.toFinset).card=5 := by simpa [support_reverse] using off
  have xro : x∉p.reverse.support := by simpa using xo
  have rx1 : 1∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo xj
  have rxi : 10-i∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo xi
  let R : OmittedComponent p.reverse :=
    ⟨H.vertices,H.nonempty,(by intro z h; simpa using H.off z h),
      (by intro z hz w hw zw; simpa using H.closed z hz w hw zw),
      H.joined⟩
  have newWhole : ∀ z∉p.reverse.support,z∈R.vertices := by
    intro u uo
    exact whole u (by simpa using uo)
  exact off_five_connected_twin_oriented table hc even conn degree rev bh ah rlen roff R hx newWhole
    (by omega) (off_five_pin_set_eq (few rev x xro) rx1 rxi (by omega))

#print axioms traceable_if_five_off_connected_twin_with_table

theorem traceable_if_five_off_connected_twin
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (hx : x∈H.vertices)
    (whole : ∀ v∉p.support,v∈H.vertices)
    (xTwo : 2≤(Pins p x).card) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  exact traceable_if_five_off_connected_twin_with_table OffFive16ConnectedTwin.row_of_signs
    hc even conn degree hp ah bh len off H hx whole xTwo
#print axioms traceable_if_five_off_connected_twin

end Graffiti189LongestPath.TwoCut.SmallOrderFour
