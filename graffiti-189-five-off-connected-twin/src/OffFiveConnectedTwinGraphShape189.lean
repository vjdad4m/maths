import OffFiveConnectedTwinBase189
import DisconnectedSingleGraphVerified

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

/-- A double porter forces a common pair of contacts for an arbitrary
omitted component, and all its double porters are universal there. -/
theorem connected_double_porter_shape
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (H : OmittedComponent p) (hx : x∈H.vertices) {i j : ℕ}
    (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j) :
    (∀ z∈H.vertices,Pins p z⊆({i,j}:Finset ℕ)) ∧
    (∀ z∈H.vertices,2≤(Pins p z).card → ∀ w∈H.vertices,w≠z → G.Adj z w) := by
  classical
  have universal (z : V) (zh : z∈H.vertices) (z2 : 2≤(Pins p z).card) :
      ∀ w∈H.vertices,w≠z → G.Adj z w := by
    obtain ⟨u,v,zu,zv,uv⟩ := two_pins_choose_ordered z2
    have hf := (two_pin_flanks_path_only hc even conn degree hp ah bh (H.off z zh) zu zv uv).1
    exact two_pin_universal_in_omitted_component hc H zh hf
  have sub : ({i,j}:Finset ℕ)⊆Pins p x := by
    intro k km
    have alt : k=i ∨ k=j := by simpa using km
    rcases alt with rfl|rfl <;> assumption
  have ca := card_le_card sub
  have x2 : 2≤(Pins p x).card := by simpa [Nat.ne_of_lt ij] using ca
  have cap := fun v => distanceTwo_le_of_even 4 v (even v)
  have bound := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp (H.off x hx)).1
  have eq : ({i,j}:Finset ℕ)=Pins p x := eq_of_subset_of_card_le sub (by simpa [Nat.ne_of_lt ij] using bound)
  refine ⟨?_,universal⟩
  intro z zh
  by_cases he : z=x
  · simpa only [he,eq] using (Subset.rfl : Pins p x⊆Pins p x)
  exact (two_pin_flanks_path_only hc even conn degree hp ah bh (H.off x hx) hi hj ij).2
    z (H.off z zh) (universal x hx x2 z zh he)

#print axioms connected_double_porter_shape


open OffFive16ConnectedTwin in
theorem off_five_connected_twin_labeling
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (hx : x∈H.vertices)
    (whole : ∀ v∉p.support,v∈H.vertices)
    {j : ℕ} (x1 : 1∈Pins p x) (xj : j∈Pins p x) :
    ∃ (φ : Fin 16→V) (C : Codes),
      Function.Injective φ ∧ Function.Surjective φ ∧ φ 11=x ∧
      (∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val) ∧
      (∀ k : Fin 16,11≤k.val → φ k∈H.vertices) ∧ goodCode j C ∧
      (∀ k : Fin 16,11≤k.val →
        (portL (code C k.val) ↔ 1∈Pins p (φ k)) ∧
        (portR (code C k.val) ↔ j∈Pins p (φ k))) := by
  classical
  have xo := H.off x hx
  let O := (univ : Finset V)\p.support.toFinset
  have oCard : O.card=5 := off
  have xoO : x∈O := by simp [O,xo]
  have more : 0<(O.erase x).card := by rw [card_erase_of_mem xoO,oCard]; decide
  obtain ⟨y,yO⟩ := card_pos.mp more
  obtain ⟨yx,yoO⟩ := mem_erase.mp yO
  have yo : y∉p.support := by simpa [O] using yoO
  obtain ⟨θ,injθ,surθ,atx,_,onP,offP⟩ :=
    order_sixteen_five_off_labeling hp len off xo yo yx.symm
  let color : V→Fin 4 := fun z => if 1∈Pins p z then
    (if j∈Pins p z then 3 else 1) else (if j∈Pins p z then 2 else 0)
  have colorL (z : V) : portL (color z) ↔ 1∈Pins p z := by
    by_cases L : 1∈Pins p z <;> by_cases R : j∈Pins p z <;> simp [color,portL,L,R]
  have colorR (z : V) : portR (color z) ↔ j∈Pins p z := by
    by_cases L : 1∈Pins p z <;> by_cases R : j∈Pins p z <;> simp [color,portR,L,R]
  let f : Fin 4→ℕ := fun k => (color (θ (off_five_tail_four k))).val
  obtain ⟨σ,mono⟩ := exists_mono_perm_fin f
  let φ : Fin 16→V := θ ∘ off_five_tail_relabel σ
  have eq (k : Fin 4) : φ (off_five_tail_four k)=θ (off_five_tail_four (σ k)) := by
    simp [φ,off_five_tail_relabel_tail]
  have inj : Function.Injective φ := injθ.comp (off_five_tail_relabel_inj σ)
  have sur : Function.Surjective φ := surθ.comp (Finite.surjective_of_injective (off_five_tail_relabel_inj σ))
  have e11 : φ 11=x := by
    change θ (off_five_tail_relabel σ 11)=x
    rw [off_five_tail_relabel_low _ _ (by decide),atx]
  have op (k : Fin 16) (kl : k.val≤10) : φ k=p.getVert k.val := by
    change θ (off_five_tail_relabel σ k)=p.getVert k.val
    rw [off_five_tail_relabel_low _ _ (by omega)]
    exact onP k kl
  have repr (k : Fin 16) (kl : 12≤k.val) : ∃ i : Fin 4,k=off_five_tail_four i := by
    refine ⟨⟨k.val-12,by have h := k.isLt; omega⟩,Fin.ext ?_⟩
    change k.val=12+(k.val-12)
    omega
  have inside (k : Fin 16) (kl : 11≤k.val) : φ k∈H.vertices := by
    by_cases e : k.val=11
    · have km : k=11 := Fin.ext e
      simpa only [km,e11] using hx
    obtain ⟨i,rfl⟩ := repr k (by omega)
    rw [eq]
    exact whole _ (offP _ (by change 11≤12+(σ i).val; omega))
  let C : Codes := (color (φ (off_five_tail_four 0)),color (φ (off_five_tail_four 1)),
    color (φ (off_five_tail_four 2)),color (φ (off_five_tail_four 3)))
  have ci (k : Fin 4) : code C (off_five_tail_four k).val=color (φ (off_five_tail_four k)) := by
    fin_cases k <;> rfl
  have cv (k : Fin 16) (kl : 11≤k.val) : code C k.val=color (φ k) := by
    by_cases k11 : k.val=11
    · have e : k=11 := Fin.ext k11
      rw [e,e11]
      change code C 11=color x
      simp [color,x1,xj,code]
    obtain ⟨i,rfl⟩ := repr k (by omega)
    exact ci i
  have pL (k : Fin 16) (kl : 11≤k.val) : portL (code C k.val) ↔ 1∈Pins p (φ k) := by
    rw [cv k kl]
    exact colorL _
  have pR (k : Fin 16) (kl : 11≤k.val) : portR (code C k.val) ↔ j∈Pins p (φ k) := by
    rw [cv k kl]
    exact colorR _
  have ordered (u v : Fin 4) (uv : u≤v) :
      color (φ (off_five_tail_four u))≤color (φ (off_five_tail_four v)) := by
    rw [eq,eq]
    exact mono uv
  have leftB : leftCount C≤2 := by
    let T := (univ : Finset (Fin 16)).filter (fun v => 11≤v.val ∧ portL (code C v.val))
    let S := T.image φ
    have so (v : V) (vs : v∈S) : v∉p.support := by
      obtain ⟨k,kt,rfl⟩ := mem_image.mp vs
      exact H.off _ (inside k (mem_filter.mp kt).2.1)
    have sp (v : V) (vs : v∈S) : 1∈Pins p v := by
      obtain ⟨k,kt,rfl⟩ := mem_image.mp vs
      exact (pL k (mem_filter.mp kt).2.1).mp (mem_filter.mp kt).2.2
    have cap := left_boundary_porters_at_most_two hc even hp ah bh (by omega) xo x1 S so sp
    change (T.image φ).card≤2 at cap
    rw [card_image_of_injective _ inj] at cap
    exact cap
  have rightB (j9 : j=9) : rightCount C≤2 := by
    let T := (univ : Finset (Fin 16)).filter (fun v => 11≤v.val ∧ portR (code C v.val))
    let S := T.image φ
    have so (v : V) (vs : v∈S) : v∉p.support := by
      obtain ⟨k,kt,rfl⟩ := mem_image.mp vs
      exact H.off _ (inside k (mem_filter.mp kt).2.1)
    have sp (v : V) (vs : v∈S) : j∈Pins p v := by
      obtain ⟨k,kt,rfl⟩ := mem_image.mp vs
      exact (pR k (mem_filter.mp kt).2.1).mp (mem_filter.mp kt).2.2
    have cap := right_boundary_porters_at_most_two hc even hp ah bh (by omega) xo xj
      (by omega) S so sp
    change (T.image φ).card≤2 at cap
    rw [card_image_of_injective _ inj] at cap
    exact cap
  have valid : goodCode j C := ⟨ordered 0 1 (by decide),ordered 1 2 (by decide),
    ordered 2 3 (by decide),leftB,rightB⟩
  exact ⟨φ,C,inj,sur,e11,op,inside,valid,fun k h => ⟨pL k h,pR k h⟩⟩

#print axioms off_five_connected_twin_labeling

open OffFive16ConnectedTwin in
private def off_five_connected_twin_mask (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : Fin 16→V) (C : Codes) : List Bool :=
  tailPairs.map fun t => if code C t.1=3 ∨ code C t.2=3 then false
    else decide (G.Adj (φ (Fin.ofNat' 16 t.1)) (φ (Fin.ofNat' 16 t.2)))

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_tail_bit
    (φ : Fin 16→V) (C : Codes) {a b : ℕ} (h : (a,b)∈tailPairs) :
    tailBit (off_five_connected_twin_mask G φ C) a b =
      (if code C a=3 ∨ code C b=3 then false
        else decide (G.Adj (φ (Fin.ofNat' 16 a)) (φ (Fin.ofNat' 16 b)))) := by
  unfold tailBit off_five_connected_twin_mask
  have bit : tailPairs[tailPairs.idxOf (a,b)]? = some (a,b) := by
    simp only [tailPairs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h <;>
      have ha := congrArg Prod.fst h <;>
      have hb := congrArg Prod.snd h <;>
      simp only [Prod.fst,Prod.snd] at ha hb <;>
      subst a <;> subst b <;> decide
  rw [List.getElem?_map,bit]
  rfl

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_mask_canonical
    (φ : Fin 16→V) (C : Codes) : canonical C (off_five_connected_twin_mask G φ C)=true := by
  apply List.all_eq_true.mpr
  intro q qm
  apply decide_eq_true
  intro h
  obtain ⟨u,v⟩ := q
  rw [off_five_connected_twin_tail_bit φ C qm,if_pos h]

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_internal
    (φ : Fin 16→V) (C : Codes)
    (univ : ∀ u v : Fin 16,11≤u.val → 11≤v.val → u≠v →
      (code C u.val=3 ∨ code C v.val=3) → G.Adj (φ u) (φ v))
    {u v : Fin 16} (uo : 11≤u.val) (uv : u.val<v.val) :
    (decide (code C u.val=3 ∨ code C v.val=3) ||
      tailBit (off_five_connected_twin_mask G φ C) u.val v.val)=true ↔ G.Adj (φ u) (φ v) := by
  by_cases h : code C u.val=3 ∨ code C v.val=3
  · have ne : u≠v := fun e => (Nat.ne_of_lt uv) (congrArg Fin.val e)
    have adj := univ u v uo (by omega) ne h
    simp [h,adj]
  have ul : 12≤u.val := by
    by_cases z : 12≤u.val
    · exact z
    · exfalso
      have t : u.val=11 := by omega
      have ct : code C u.val=3 := by rw [t]; rfl
      exact h (.inl ct)
  have vl := v.isLt
  have pair : (u.val,v.val)∈tailPairs := by
    have alt : (u.val=12 ∧ v.val=13) ∨ (u.val=12 ∧ v.val=14) ∨
      (u.val=12 ∧ v.val=15) ∨ (u.val=13 ∧ v.val=14) ∨ (u.val=13 ∧ v.val=15) ∨
      (u.val=14 ∧ v.val=15) := by omega
    rcases alt with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩ <;> simp [tailPairs,a,b]
  have ue : Fin.ofNat' 16 u.val=u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
  have ve : Fin.ofNat' 16 v.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  rw [off_five_connected_twin_tail_bit φ C pair,if_neg h,ue,ve]
  simp [h]

#print axioms off_five_connected_twin_internal

end Graffiti189LongestPath.TwoCut.SmallOrderFour
