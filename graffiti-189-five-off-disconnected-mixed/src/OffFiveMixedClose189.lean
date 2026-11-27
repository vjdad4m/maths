import OffFiveMixedMarks189
import OffFiveDisconnectedFoundation189
import OffFiveMixedShape189
import OffFiveLabeling189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data pin_pos dist_two mem_distanceTwo no_endpoints same_support_optimal reverse_long reverse_pin from SmallOrderFour189
open private omittedNeighbors omittedDegree_eq hamilton_of_labeled_chain from FourOffGraphCore189
open private omitted_degree_component_bound length_ten_two_pin_shape two_pin_flanks_path_only from FourOffGraphSupport189
open private off_five_disconnected_mixed_marks off_five_mixed_model_forward off_five_mixed_model_exact from OffFiveMixedMarks189

open OffFive16DisconnectedMixed in
private theorem off_five_model_d2_image
    (hc : G.Connected) (m : Marks) (ψ : Fin 13→V) (inj : Function.Injective ψ)
    (forw : ∀ v w,edge m v w=true → G.Adj (ψ v) (ψ w))
    (z : Fin 13) (exactAt : ∀ v,G.Adj (ψ z) (ψ v) → edge m z v=true) :
    (two m z).image ψ ⊆ DistanceTwo G (ψ z) := by
  intro w hw
  obtain ⟨v,v2,rfl⟩ := mem_image.mp hw
  obtain ⟨vne,no,q,zq,qv⟩ := (mem_filter.mp v2).2
  have neq : ψ z≠ψ v := fun e => vne (inj e).symm
  have nadj : ¬G.Adj (ψ z) (ψ v) := fun e => by
    have hm := exactAt v e
    simp [hm] at no
  exact mem_distanceTwo.mpr (dist_two hc neq nadj (forw z q zq) (forw q v qv))

open OffFive16DisconnectedMixed in
private theorem off_five_model_d2_cap (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5) (m : Marks) (ψ : Fin 13→V)
    (inj : Function.Injective ψ) (forw : ∀ v w,edge m v w=true → G.Adj (ψ v) (ψ w))
    (z : Fin 13) (exactAt : ∀ v,G.Adj (ψ z) (ψ v) → edge m z v=true) :
    (two m z).card≤4 := by
  have c := card_le_card (off_five_model_d2_image hc m ψ inj forw z exactAt)
  rw [card_image_of_injective _ inj] at c
  exact c.trans (distanceTwo_le_of_even 4 (ψ z) (even _))

open OffFive16DisconnectedMixed in
private theorem off_five_mixed_force_inner_port
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (ψ : Fin 13→V) (inj : Function.Injective ψ)
    (value : ∀ k : Fin 13,k.val≤10 → ψ k=p.getVert k.val)
    (x11 : ψ 11=x) (y12 : ψ 12=y) (_xo : x∉p.support)
    (x1 : 1∈Pins p x) (x8 : 8∈Pins p x)
    (isolated : ∀ w∉p.support,¬G.Adj x w)
    (onlyPath : ∀ w∈DistanceTwo G x,w∈p.support)
    (m : Marks) (r : ℕ) (sat : center_cap m) (see : othersSeeEnd m r)
    (forw : ∀ v w,edge m v w=true → G.Adj (ψ v) (ψ w))
    (leftE : ∀ v,G.Adj (ψ 0) (ψ v) → edge m 0 v=true)
    (rightE : ∀ v,G.Adj (ψ 10) (ψ v) → edge m 10 v=true)
    {z : V} (zo : z∉p.support) (zx : z≠x) (zy : z≠y) :
    Pins p z⊆({r}:Finset ℕ) := by
  have notLabels (v : Fin 13) : ψ v≠z := by
    intro e
    have vv := v.isLt
    have aux : v.val≤10 ∨ v.val=11 ∨ v.val=12 := by omega
    rcases aux with on|e1|e2
    · exact zo (e ▸ ((value v on).symm ▸ p.getVert_mem_support v.val))
    · have ve : v=11 := Fin.ext e1
      rw [ve,x11] at e
      exact zx e.symm
    · have ve : v=12 := Fin.ext e2
      rw [ve,y12] at e
      exact zy e.symm
  have full (c : Fin 13) (cc : (two m c).card=4)
      (C : ∀ v,G.Adj (ψ c) (ψ v) → edge m c v=true) :
      ¬z∈DistanceTwo G (ψ c) := by
    intro zd
    have sub := off_five_model_d2_image hc m ψ inj forw c C
    have eq : (two m c).image ψ=DistanceTwo G (ψ c) :=
      eq_of_subset_of_card_le sub (by
        rw [card_image_of_injective _ inj,cc]
        exact distanceTwo_le_of_even 4 (ψ c) (even _))
    rw [←eq] at zd
    obtain ⟨k,_,ke⟩ := mem_image.mp zd
    exact notLabels k ke
  have leftNo := full 0 sat.1 leftE
  have rightNo := full 10 sat.2 rightE
  have a0 : ψ 0=a := by rw [value 0 (by decide)]; exact p.getVert_zero
  have b10 : ψ 10=b := by rw [value 10 (by decide)]; simpa only [len] using p.getVert_length
  have noEnd (a : V) (on : a∈p.support) (n : ¬G.Adj z a) {k : ℕ}
      (zk : k∈Pins p z) (ak : G.Adj a (p.getVert k)) : z∈DistanceTwo G a :=
    mem_distanceTwo.mpr (dist_two hc (fun e => zo (e ▸ on)) (fun e => n e.symm) ak (pin_data zk).2.symm)
  intro k zk
  have kb := (pin_data zk).1
  have kp := pin_pos hp zo zk
  have dis {h : ℕ} (hx : h∈Pins p x) (hz : h∈Pins p z) : False :=
    zo (onlyPath z (mem_distanceTwo.mpr (dist_two hc zx.symm (isolated z zo) (pin_data hx).2 (pin_data hz).2.symm)))
  have k1 : k≠1 := fun e => dis (e.symm ▸ x1) zk
  have k8 : k≠8 := fun e => dis (e.symm ▸ x8) zk
  apply mem_singleton.mpr
  by_contra kr
  let u : Fin 13 := ⟨k,by omega⟩
  have uv : ψ u=p.getVert k := value u (by change k≤10; omega)
  rcases see u (by change 1≤k; omega) (by change k≤9; omega) k1 k8 kr with le|re
  · have ak := forw 0 u le
    rw [a0,uv] at ak
    exact leftNo (a0.symm ▸ noEnd a p.start_mem_support (no_endpoints hp zo).1 zk ak)
  · have bk := forw 10 u re
    rw [b10,uv] at bk
    exact rightNo (b10.symm ▸ noEnd b p.end_mem_support (no_endpoints hp zo).2 zk bk)

#print axioms off_five_mixed_force_inner_port

private theorem one_port_high_complete_in_four
    {a b w : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (h4 : H.vertices.card=4) (wH : w∈H.vertices)
    (deg : 4≤G.degree w) {r : ℕ} (port : Pins p w⊆({r}:Finset ℕ)) :
    r∈Pins p w ∧ ∀ z∈H.vertices,z≠w → G.Adj w z := by
  classical
  have pl : (Pins p w).card≤1 := (card_le_card port).trans_eq (card_singleton _)
  have fact := omitted_degree_component_bound hp H wH
  have non : 0<(Pins p w).card := by omega
  obtain ⟨k,kp⟩ := card_pos.mp non
  have eq : k=r := mem_singleton.mp (port kp)
  refine ⟨eq ▸ kp,?_⟩
  intro z zH zw
  by_contra no
  let I := H.vertices.erase w
  have zI : z∈I := mem_erase.mpr ⟨zw,zH⟩
  have size : (I.erase z).card=2 := by
    rw [card_erase_of_mem zI,show I.card=3 by rw [show I=H.vertices.erase w from rfl,card_erase_of_mem wH,h4]]
  have sub : omittedNeighbors p w⊆I.erase z := by
    intro v vH
    obtain ⟨e,vo⟩ := mem_filter.mp vH
    have av := (mem_neighborFinset G w v).mp e
    have a : v∈H.vertices := by
      by_contra t
      exact vo (H.closed w wH v t av)
    exact mem_erase.mpr ⟨(fun h => no (h ▸ av)),mem_erase.mpr ⟨(fun h => G.loopless _ (h ▸ av)),a⟩⟩
  have cap := (card_le_card sub).trans_eq size
  have split := omittedDegree_eq hp (H.off w wH)
  omega

open OffFive16DisconnectedMixed in
private theorem off_five_mixed_full_path_lift
    {a b y : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (h4 : H.vertices.card=4)
    (high : ∀ z∈H.vertices,4≤G.degree z) (yh : y∈H.vertices)
    (φ : Fin 16→V) (inj : Function.Injective φ) (sur : Function.Surjective φ)
    (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val) (at12 : φ 12=y)
    (inside : ∀ k : Fin 16,13≤k.val → φ k∈H.vertices)
    (m : Marks) (r : ℕ) (rb : r≤10)
    (each : ∀ k : Fin 16,13≤k.val → Pins p (φ k)⊆({r}:Finset ℕ))
    (positive : ∀ v w : Fin 13, edge m v w=true →
      G.Adj (φ (Fin.castLE (by decide : 13≤16) v)) (φ (Fin.castLE (by decide : 13≤16) w)))
    (l : List (Fin 16)) (path : FullPath m r l) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  have high4 (w : Fin 16) (wh : 13≤w.val) :=
    one_port_high_complete_in_four hp H h4 (inside w wh) (high _ (inside w wh)) (each w wh)
  have Hmem (z : Fin 16) (za : 12≤z.val) : φ z∈H.vertices := by
    by_cases hi : 13≤z.val
    · exact inside _ hi
    have ze : z=12 := Fin.ext (by change z.val=12; omega)
    simpa only [ze,at12] using yh
  have rel (v w : Fin 16) (e : edgeFull m r v w=true) : G.Adj (φ v) (φ w) := by
    simp only [edgeFull,Bool.or_eq_true,decide_eq_true_eq] at e
    rcases e with ((base|⟨vH,wH,ne⟩)|outer)
    · by_cases q : v.val<13 ∧ w.val<13
      · simp only [dif_pos q] at base
        exact positive ⟨v.val,q.1⟩ ⟨w.val,q.2⟩ base
      · simp only [dif_neg q] at base
        contradiction
    · have Ne : φ v≠φ w := fun e => ne (inj e)
      by_cases hi : 13≤v.val
      · exact (high4 v hi).2 _ (Hmem w wH) Ne.symm
      have hj : 13≤w.val := by
        by_contra! no
        exact ne (Fin.ext (by omega))
      exact ((high4 w hj).2 _ (Hmem v vH) Ne).symm
    · rcases outer with ⟨vr,wh⟩|⟨wr,vh⟩
      · rw [value v (by omega),vr]
        exact (pin_data (high4 w wh).1).2.symm
      · rw [value w (by omega),wr]
        exact (pin_data (high4 v vh).1).2
  letI : Nonempty V := ⟨a⟩
  exact hamilton_of_labeled_chain φ inj sur l path.1 path.2.1 (path.2.2.imp rel)

#print axioms one_port_high_complete_in_four
#print axioms off_five_mixed_full_path_lift

private theorem off_five_pin_set_eq {a b x : V} {p : G.Walk a b} {i j : ℕ}
    (few : (Pins p x).card≤2) (hi : i∈Pins p x) (hj : j∈Pins p x) (ne : i≠j) :
    Pins p x=({i,j}:Finset ℕ) := by
  symm
  apply eq_of_subset_of_card_le
  · intro k hk
    have alt : k=i ∨ k=j := by simpa using hk
    rcases alt with rfl|rfl <;> assumption
  · simpa [ne] using few

open OffFive16DisconnectedMixed in
private theorem off_five_disconnected_mixed_oriented
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (h4 : H.vertices.card=4) (high : ∀ z∈H.vertices,4≤G.degree z)
    (xo : x∉p.support) (xh : x∉H.vertices) (yh : y∈H.vertices)
    (whole : ∀ z∉p.support,z=x ∨ z∈H.vertices)
    (isolated : ∀ z∉p.support,¬G.Adj x z)
    (xPins : Pins p x=({1,8}:Finset ℕ)) (yPins : Pins p y=({2,9}:Finset ℕ)) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have yo := H.off y yh
  have xy : x≠y := fun e => xh (e.symm ▸ yh)
  have x1 : 1∈Pins p x := by rw [xPins]; decide
  have x8 : 8∈Pins p x := by rw [xPins]; decide
  have y2 : 2∈Pins p y := by rw [yPins]; decide
  have y9 : 9∈Pins p y := by rw [yPins]; decide
  have hole := (length_ten_two_pin_shape hc even conn degree hp ah bh len xo x1 x8 (by decide)).2.2 (by decide)
  have only := (two_pin_flanks_path_only hc even conn degree hp ah bh xo x1 x8 (by decide)).1
  obtain ⟨m,m0,m9,hm,nz,c1,c2,L,R⟩ :=
    off_five_disconnected_mixed_marks hp.1 ah bh len xo x1 hole.1 hole.2
  obtain ⟨φ,inj,sur,at11,at12,onP,offP⟩ := order_sixteen_five_off_labeling hp.1 len off xo yo xy
  let ψ : Fin 13→V := fun v => φ (Fin.castLE (by decide : 13≤16) v)
  have inj13 : Function.Injective ψ := by
    intro v w h
    exact Fin.ext (congrArg (fun k : Fin 16 => k.val) (inj h))
  have val13 (k : Fin 13) (kv : k.val≤10) : ψ k=p.getVert k.val :=
    onP (Fin.castLE (by decide : 13≤16) k) kv
  have atψ11 : ψ 11=x := at11
  have atψ12 : ψ 12=y := at12
  have fw := off_five_mixed_model_forward len ψ val13 atψ11 atψ12 x1 x8 y2 y9 m L R
  obtain ⟨E0,E10,E11,E12⟩ := off_five_mixed_model_exact hp.1 len ψ val13 atψ11 atψ12 xo yo
    (isolated y yo) xPins yPins m L R
  have cap (z : Fin 13) (ez : ∀ v,G.Adj (ψ z) (ψ v) → edge m z v=true) :=
    off_five_model_d2_cap hc even m ψ inj13 fw z ez
  have signs := classify m m0 m9 (hm 1 (.inl rfl)) (hm 8 (.inr rfl)) nz c1 c2
    (cap 0 E0) (cap 10 E10) (cap 11 E11) (cap 12 E12)
  have notx (k : Fin 16) (kl : 13≤k.val) : φ k≠x := by
    intro e
    have n := congrArg Fin.val (inj (e.trans at11.symm))
    change k.val=11 at n
    omega
  have noty (k : Fin 16) (kl : 13≤k.val) : φ k≠y := by
    intro e
    have n := congrArg Fin.val (inj (e.trans at12.symm))
    change k.val=12 at n
    omega
  have inside (k : Fin 16) (kl : 13≤k.val) : φ k∈H.vertices :=
    (whole _ (offP _ (by omega))).resolve_left (notx k kl)
  have finish (r : ℕ) (r10 : r≤10) (sat : center_cap m) (see : othersSeeEnd m r)
      (l : List (Fin 16)) (path : FullPath m r l) :
      ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
    have each (k : Fin 16) (kl : 13≤k.val) : Pins p (φ k)⊆({r}:Finset ℕ) :=
      off_five_mixed_force_inner_port hc even hp.1 len ψ inj13 val13 atψ11 atψ12 xo x1 x8 isolated only
        m r sat see fw E0 E10 (offP _ (by omega)) (notx k kl) (noty k kl)
    exact off_five_mixed_full_path_lift hp.1 H h4 high yh φ inj sur onP at12 inside m r r10 each fw l path
  rcases signs with ma|mb
  · subst m
    exact finish aPort (by decide) a_cap a_see pathA a_path
  · subst m
    exact finish bPort (by decide) b_cap b_see pathB b_path

#print axioms off_five_disconnected_mixed_oriented

/-- Order sixteen, five omitted vertices: disconnected omitted graph and
a double porter in the nontrivial omitted component. -/
theorem traceable_if_five_off_disconnected_mixed
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (disc : ¬∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices)
    (hasTwo : ∃ y∉p.support,2≤(Pins p y).card ∧ ∃ z∉p.support,G.Adj y z) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have cap := fun v => distanceTwo_le_of_even 4 v (even v)
  have few {a b : V} {q : G.Walk a b} (opt : EdgeOptimal q)
      (z : V) (zo : z∉q.support) : (Pins q z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree opt zo).1
  obtain ⟨H,x,xo,xh,h4,high,whole⟩ := off_five_disconnected_shape degree hp.1 off (few hp) disc
  obtain ⟨xt,isolated⟩ := singleton_pins_of_off_five_disconnected conn hp.1 H xo xh whole (few hp x xo)
  obtain ⟨y,yo,yt,z,zo,yz⟩ := hasTwo
  have yx : y≠x := fun e => isolated z zo (e ▸ yz)
  have yh := (whole y yo).resolve_left yx
  have forms := (off_five_mixed_forced_pins hc even conn degree hp ah bh len xo yo
    yx.symm (isolated y yo) xt.ge yt).1
  rcases forms with ⟨x1,x8,y2,y9⟩|⟨x2,x9,y1,y8⟩
  · exact off_five_disconnected_mixed_oriented hc even conn degree hp ah bh len off H h4 high xo xh yh
      whole isolated (off_five_pin_set_eq (few hp x xo) x1 x8 (by decide))
      (off_five_pin_set_eq (few hp y yo) y2 y9 (by decide))
  have rev : EdgeOptimal p.reverse :=
    same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have rlen : p.reverse.length=10 := by simpa using len
  have roff : ((univ : Finset V)\p.reverse.support.toFinset).card=5 := by simpa [support_reverse] using off
  have xro : x∉p.reverse.support := by simpa using xo
  have yro : y∉p.reverse.support := by simpa using yo
  have rx1 : 1∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo x9
  have rx8 : 8∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo x2
  have ry2 : 2∈Pins p.reverse y := by simpa [len] using reverse_pin hp.1 yo y8
  have ry9 : 9∈Pins p.reverse y := by simpa [len] using reverse_pin hp.1 yo y1
  let R : OmittedComponent p.reverse :=
    ⟨H.vertices,H.nonempty,(by intro z h; simpa using H.off z h),
      (by intro z hz w hw zw; simpa using H.closed z hz w hw zw),
      H.joined⟩
  have newWhole : ∀ z∉p.reverse.support,z=x ∨ z∈R.vertices := by
    intro u uo
    exact whole u (by simpa using uo)
  have newIsolated : ∀ z∉p.reverse.support,¬G.Adj x z := by
    intro u uo
    exact isolated u (by simpa using uo)
  exact off_five_disconnected_mixed_oriented hc even conn degree rev bh ah rlen roff R h4 high xro xh yh
    newWhole newIsolated (off_five_pin_set_eq (few rev x xro) rx1 rx8 (by decide))
    (off_five_pin_set_eq (few rev y yro) ry2 ry9 (by decide))

#print axioms traceable_if_five_off_disconnected_mixed

end Graffiti189LongestPath.TwoCut.SmallOrderFour
