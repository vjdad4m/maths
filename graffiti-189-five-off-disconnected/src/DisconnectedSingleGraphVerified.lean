import OffFiveDiscSingleTable189
import OffFiveMixedClose189
import Mathlib.Data.List.Sort
namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data pin_pos pin_of_neighbor_mem LeftMarks RightMarks mark_length card_leftMarks card_rightMarks mem_distanceTwo dist_two no_endpoints same_support_optimal reverse_long reverse_pin from SmallOrderFour189
open private mark_length_ten_at_most_two_holes omitted_degree_component_bound two_pin_flanks_path_only length_ten_two_pin_shape pins_gap_at_four from FourOffGraphSupport189
open private one_port_high_complete_in_four off_five_pin_set_eq from OffFiveMixedClose189
open private hamilton_of_labeled_chain omittedNeighbors omittedDegree_eq two_pins_choose_ordered from FourOffGraphCore189
open private path_neighbor_is_pin_of_off from OffFiveMixedMarks189


open OffFive16DisconnectedSingle in
private theorem off_five_single_pre_forward
    {a b x : V} {p : G.Walk a b} (len : p.length=10) {j : ℕ} (jhi : j≤9)
    (ψ : Fin 12→V) (value : ∀ k : Fin 12,k.val≤10 → ψ k=p.getVert k.val)
    (x11 : ψ 11=x) (x1 : 1∈Pins p x) (xj : j∈Pins p x)
    (m : Marks)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    ∀ v w,edge j m v w=true → G.Adj (ψ v) (ψ w) := by
  have direction (v w : Fin 12) (h : dir j m v w=true) : G.Adj (ψ v) (ψ w) := by
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with (((ha|⟨hx,h11⟩)|he)|hf)
    · rw [value v (by omega),value w ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · have w11 : w=11 := Fin.ext h11
      rw [value v (by omega),w11,x11]
      rcases hx with h|h
      · rw [h]; exact (pin_data x1).2.symm
      · rw [h]; exact (pin_data xj).2.symm
    · by_cases q : v.val=0 ∧ 1≤w.val ∧ w.val≤10
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [value v (by omega),value w q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨w.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (w.val-1+1)) at h
        rwa [show w.val-1+1=w.val by omega] at h
      · simp only [dif_neg q] at he
        contradiction
    · by_cases q : w.val=10 ∧ v.val<10
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [value v (by omega),value w (by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨v.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        contradiction
  intro v w h
  simp only [edge,Bool.or_eq_true] at h
  exact h.elim (direction _ _) (fun e => (direction _ _ e).symm)

open OffFive16DisconnectedSingle in
private theorem off_five_single_pre_exact
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10) (j : ℕ)
    (ψ : Fin 12→V) (value : ∀ k : Fin 12,k.val≤10 → ψ k=p.getVert k.val)
    (x11 : ψ 11=x) (xo : x∉p.support) (xPins : Pins p x=({1,j}:Finset ℕ))
    (m : Marks)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    (∀ v,G.Adj (ψ 0) (ψ v) → edge j m 0 v=true) ∧
    (∀ v,G.Adj (ψ 10) (ψ v) → edge j m 10 v=true) ∧
    (∀ v,G.Adj (ψ 11) (ψ v) → edge j m 11 v=true) := by
  have a0 : ψ 0=a := by rw [value 0 (by decide)]; exact p.getVert_zero
  have b10 : ψ 10=b := by rw [value 10 (by decide)]; simpa only [len] using p.getVert_length
  have pathV (v : Fin 12) (ne : v≠11) : v.val≤10 := by
    have h := v.isLt
    by_contra! bad
    exact ne (Fin.ext (by change v.val=11; omega))
  refine ⟨?_,?_,?_⟩
  · intro v va
    have vp := pathV v (fun e => (no_endpoints hp xo).1 (by rw [e,x11,a0] at va; exact va.symm))
    have up : 1≤v.val := by
      by_cases yes : 1≤v.val
      · exact yes
      · have ev : v=0 := Fin.ext (by change v.val=0; omega)
        exact False.elim (G.loopless _ (ev ▸ va))
    have q : (0:Fin 12).val=0 ∧ 1≤v.val ∧ v.val≤10 := ⟨rfl,up,vp⟩
    have ia : G.Adj a (p.getVert ((v.val-1)+1)) := by
      rw [show v.val-1+1=v.val by omega,←value v vp,←a0]
      exact va
    have h : m ⟨v.val-1,by omega⟩=1 := (L _).mpr ia
    simp only [edge,Bool.or_eq_true]
    left
    simp only [dir,Bool.or_eq_true]
    exact .inl (.inr (by simp only [dif_pos q,decide_eq_true_eq,h]))
  · intro v vb
    have vp := pathV v (fun e => (no_endpoints hp xo).2 (by rw [e,x11,b10] at vb; exact vb.symm))
    have up : v.val<10 := by
      by_cases yes : v.val<10
      · exact yes
      · have ev : v=10 := Fin.ext (by change v.val=10; omega)
        exact False.elim (G.loopless _ (ev ▸ vb))
    have q : (10:Fin 12).val=10 ∧ v.val<10 := ⟨rfl,up⟩
    have ib : G.Adj b (p.getVert v.val) := by rw [←value v vp,←b10]; exact vb
    have h : m ⟨v.val,up⟩=2 := (R _).mpr ib
    simp only [edge,Bool.or_eq_true]
    right
    simp only [dir,Bool.or_eq_true]
    exact .inr (by simp only [dif_pos q,decide_eq_true_eq,h])
  · intro v vx
    have vp := pathV v (fun e => G.loopless _ (e ▸ vx))
    have pi := path_neighbor_is_pin_of_off hp xo (show v.val≤p.length by omega)
      (by rwa [←value v vp,←x11])
    have p1 : v.val=1 ∨ v.val=j := by simpa [xPins] using pi
    simp only [edge,Bool.or_eq_true]
    right
    simp only [dir,Bool.or_eq_true,decide_eq_true_eq]
    exact .inl (.inl (.inr ⟨p1,rfl⟩))

#print axioms off_five_single_pre_forward
#print axioms off_five_single_pre_exact

private theorem model_d2_cap_any {n : ℕ} (hc : G.Connected)
    (even : ∀ v,(EvenFrom G v).card≤5) (E : Fin n→Fin n→Bool) (φ : Fin n→V)
    (inj : Function.Injective φ) (forw : ∀ v w,E v w=true → G.Adj (φ v) (φ w))
    (z : Fin n) (rev : ∀ v,G.Adj (φ z) (φ v) → E z v=true) :
    (univ.filter fun y => y≠z ∧ !E z y=true ∧
      ∃ w : Fin n,E z w=true ∧ E w y=true).card≤4 := by
  let S := univ.filter fun y => y≠z ∧ !E z y=true ∧
    ∃ w : Fin n,E z w=true ∧ E w y=true
  have sub : S.image φ ⊆ DistanceTwo G (φ z) := by
    intro x xmem
    obtain ⟨v,vS,rfl⟩ := mem_image.mp xmem
    obtain ⟨ne,no,w,zw,wv⟩ := (mem_filter.mp vS).2
    have na : ¬G.Adj (φ z) (φ v) := fun e => by have r := rev v e; simp [r] at no
    exact mem_distanceTwo.mpr (dist_two hc (fun e => ne (inj e).symm) na (forw z w zw) (forw w v wv))
  have b := card_le_card sub
  rw [card_image_of_injective _ inj] at b
  exact b.trans (distanceTwo_le_of_even 4 (φ z) (even _))

open OffFive16DisconnectedSingle in
private theorem off_five_single_core_base
    (j : ℕ) (m : Marks) (P : Tuple) {v w : Fin 16}
    (vl : v.val<12) (wl : w.val<12)
    (h : edge j m ⟨v.val,vl⟩ ⟨w.val,wl⟩=true) :
    coreEdge j m P v w=true := by
  simp only [edge,Bool.or_eq_true] at h
  have vw : v.val<12 ∧ w.val<12 := ⟨vl,wl⟩
  have wv : w.val<12 ∧ v.val<12 := ⟨wl,vl⟩
  simp only [coreEdge,coreDir,Bool.or_eq_true,dif_pos vw,dif_pos wv]
  exact h.elim (fun e => .inl (.inl (.inl e))) (fun e => .inr (.inl (.inl e)))

open OffFive16DisconnectedSingle in
private theorem off_five_single_core_forward
    {a b : V} {p : G.Walk a b}
    (H : OmittedComponent p) (φ : Fin 16→V) (inj : Function.Injective φ)
    (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (inside : ∀ k : Fin 16,12≤k.val → φ k∈H.vertices)
    (clique : ∀ u∈H.vertices,∀ v∈H.vertices,u≠v → G.Adj u v)
    (j : ℕ) (m : Marks) (P : Tuple)
    (exactPin : ∀ k : Fin 16,12≤k.val → Pins p (φ k)=({port P k.val}:Finset ℕ))
    (portBound : ∀ k : Fin 16,12≤k.val → port P k.val≤9)
    (baseForward : ∀ v w : Fin 12,edge j m v w=true →
      G.Adj (φ (Fin.castLE (by decide : 12≤16) v)) (φ (Fin.castLE (by decide : 12≤16) w))) :
    ∀ v w,coreEdge j m P v w=true → G.Adj (φ v) (φ w) := by
  have dir (v w : Fin 16) (e : coreDir j m P v w=true) : G.Adj (φ v) (φ w) := by
    simp only [coreDir,Bool.or_eq_true,decide_eq_true_eq] at e
    rcases e with ((base|⟨vl,vw⟩)|⟨vr,wl⟩)
    · by_cases d : v.val<12 ∧ w.val<12
      · simp only [dif_pos d] at base
        have d' : edge j m ⟨v.val,d.1⟩ ⟨w.val,d.2⟩=true := by
          simp [edge,base]
        exact baseForward _ _ d'
      · simp only [dif_neg d] at base
        contradiction
    · exact clique _ (inside v vl) _ (inside w (by omega))
        (fun e => (Nat.ne_of_lt vw) (congrArg Fin.val (inj e)))
    · have pin : port P w.val∈Pins p (φ w) := by rw [exactPin w wl]; simp
      have vv := portBound w wl
      rw [value v (by omega),vr]
      exact (pin_data pin).2.symm
  intro v w e
  simp only [coreEdge,Bool.or_eq_true] at e
  exact e.elim (dir _ _) (fun r => (dir _ _ r).symm)

open OffFive16DisconnectedSingle in
private theorem off_five_single_core_exact_high
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (φ : Fin 16→V) (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (at11 : φ 11=x) (P : Tuple)
    (offH : ∀ k : Fin 16,12≤k.val → φ k∉p.support)
    (isolated : ∀ z∉p.support,¬G.Adj x z)
    (exactPin : ∀ k : Fin 16,12≤k.val → Pins p (φ k)=({port P k.val}:Finset ℕ))
    (j : ℕ) (m : Marks) (u : Fin 16) (uh : 12≤u.val) :
    ∀ v,G.Adj (φ u) (φ v) → coreEdge j m P u v=true := by
  intro v e
  by_cases large : 12≤v.val
  · have ne : u.val≠v.val := fun h => G.loopless _ ((Fin.ext h : u=v) ▸ e)
    rcases lt_or_gt_of_ne ne with h|h
    · simp only [coreEdge,Bool.or_eq_true]
      left
      simp only [coreDir,Bool.or_eq_true,decide_eq_true_eq]
      exact .inl (.inr ⟨uh,h⟩)
    · simp only [coreEdge,Bool.or_eq_true]
      right
      simp only [coreDir,Bool.or_eq_true,decide_eq_true_eq]
      exact .inl (.inr ⟨large,h⟩)
  have small : v.val≤10 := by
    by_cases yes : v.val≤10
    · exact yes
    · have eq : v=11 := Fin.ext (by change v.val=11; omega)
      exact False.elim (isolated _ (offH u uh) (by rw [eq,at11] at e; exact e.symm))
  have pin := path_neighbor_is_pin_of_off hp (offH u uh) (show v.val≤p.length by omega)
    (by rwa [←value v small])
  have r : v.val=port P u.val := mem_singleton.mp ((exactPin u uh) ▸ pin)
  simp only [coreEdge,Bool.or_eq_true]
  right
  simp only [coreDir,Bool.or_eq_true,decide_eq_true_eq]
  exact .inr ⟨r,uh⟩

open OffFive16DisconnectedSingle in
private theorem off_five_single_core_exact_low
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (φ : Fin 16→V) (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (at11 : φ 11=x)
    (offH : ∀ k : Fin 16,12≤k.val → φ k∉p.support)
    (isolated : ∀ z∉p.support,¬G.Adj x z)
    (j : ℕ) (m : Marks) (P : Tuple) (u : Fin 12) (low : u=0 ∨ u=10 ∨ u=11)
    (exactAt : ∀ v : Fin 12,G.Adj (φ (Fin.castLE (by decide : 12≤16) u))
      (φ (Fin.castLE (by decide : 12≤16) v)) → edge j m u v=true) :
    ∀ w,G.Adj (φ (Fin.castLE (by decide : 12≤16) u)) (φ w) →
      coreEdge j m P (Fin.castLE (by decide : 12≤16) u) w=true := by
  intro w e
  have wl : w.val<12 := by
    by_cases yes : w.val<12
    · exact yes
    · exfalso
      have wo := offH w (by omega)
      rcases low with rfl|rfl|rfl
      · have ea : φ (Fin.castLE (by decide : 12≤16) (0:Fin 12))=a :=
          (value 0 (by decide)).trans p.getVert_zero
        exact (no_endpoints hp wo).1 (ea ▸ e.symm)
      · have eb : φ (Fin.castLE (by decide : 12≤16) (10:Fin 12))=b := by
          change φ 10=b
          rw [value 10 (by decide)]
          simpa only [len] using p.getVert_length
        exact (no_endpoints hp wo).2 (eb ▸ e.symm)
      · exact isolated _ wo (at11 ▸ e)
  exact off_five_single_core_base j m P u.isLt wl (exactAt ⟨w.val,wl⟩ e)

#print axioms off_five_single_core_forward
#print axioms off_five_single_core_exact_high
#print axioms off_five_single_core_exact_low

/-- Sort finitely many indices by a numeric key without changing labels
outside the specified domain. -/
theorem exists_mono_perm_fin {n : ℕ} (f : Fin n→ℕ) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (fun i => f (σ i)) := by
  let le := fun x y : Fin n => decide (f x≤f y)
  let L := (List.finRange n).mergeSort le
  have perm : L.Perm (List.finRange n) := List.mergeSort_perm _ _
  have len : L.length=n := by simpa using perm.length_eq
  have nd : L.Nodup := perm.nodup_iff.mpr (List.nodup_finRange n)
  let g : Fin n→Fin n := fun i => L[i.val]'(by rw [len]; exact i.isLt)
  have inj : Function.Injective g := by
    intro u v eq
    apply Fin.ext
    exact nd.getElem_inj_iff.mp eq
  let σ : Fin n ≃ Fin n := Equiv.ofBijective g ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨σ,?_⟩
  have sorted : L.Pairwise (fun u v => f u≤f v) := by
    have trans (a b c : Fin n) (ha : le a b=true) (hb : le b c=true) : le a c=true :=
      decide_eq_true (le_trans (of_decide_eq_true ha) (of_decide_eq_true hb))
    have total (a b : Fin n) : le a b || le b a := by
      simp [le,le_total]
    simpa [le] using List.sorted_mergeSort trans total (List.finRange n)
  intro a b leab
  by_cases e : a=b
  · simp [e]
  have al : a.val<L.length := by rw [len]; exact a.isLt
  have bl : b.val<L.length := by rw [len]; exact b.isLt
  have hlt : a.val<b.val := lt_of_le_of_ne leab (fun ee => e (Fin.ext ee))
  exact List.pairwise_iff_getElem.mp sorted a.val b.val al bl hlt

#print axioms exists_mono_perm_fin

private def off_five_tail_four (i : Fin 4) : Fin 16 :=
  ⟨12+i.val,by have h := i.isLt; omega⟩

private def off_five_tail_relabel (σ : Equiv.Perm (Fin 4)) (v : Fin 16) : Fin 16 :=
  if h : v.val<12 then v else
    off_five_tail_four (σ ⟨v.val-12,by have k := v.isLt; omega⟩)

private theorem off_five_tail_relabel_low (σ : Equiv.Perm (Fin 4)) (v : Fin 16)
    (h : v.val<12) : off_five_tail_relabel σ v=v := by simp [off_five_tail_relabel,h]

private theorem off_five_tail_relabel_tail (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    off_five_tail_relabel σ (off_five_tail_four i)=off_five_tail_four (σ i) := by
  have no : ¬(off_five_tail_four i).val<12 := by change ¬(12+i.val<12); omega
  unfold off_five_tail_relabel
  rw [dif_neg no]
  congr 2
  exact Fin.ext (by change 12+i.val-12=i.val; omega)

private theorem off_five_tail_relabel_inj (σ : Equiv.Perm (Fin 4)) :
    Function.Injective (off_five_tail_relabel σ) := by
  intro u v h
  by_cases ul : u.val<12 <;> by_cases vl : v.val<12
  · rwa [off_five_tail_relabel_low _ _ ul,off_five_tail_relabel_low _ _ vl] at h
  · rw [off_five_tail_relabel_low _ _ ul,off_five_tail_relabel,dif_neg vl] at h
    have q := congrArg Fin.val h
    change u.val=12+(σ ⟨v.val-12,by have vv := v.isLt; omega⟩).val at q
    omega
  · rw [off_five_tail_relabel_low _ _ vl,off_five_tail_relabel,dif_neg ul] at h
    have q := congrArg Fin.val h
    change 12+(σ ⟨u.val-12,by have uu := u.isLt; omega⟩).val=v.val at q
    omega
  rw [off_five_tail_relabel,off_five_tail_relabel,dif_neg ul,dif_neg vl] at h
  have q := congrArg Fin.val h
  change 12+(σ ⟨u.val-12,by have uu := u.isLt; omega⟩).val=
    12+(σ ⟨v.val-12,by have vv := v.isLt; omega⟩).val at q
  have r := σ.injective (Fin.ext (show
    (σ ⟨u.val-12,by have uu := u.isLt; omega⟩).val =
    (σ ⟨v.val-12,by have vv := v.isLt; omega⟩).val by omega))
  have t := congrArg Fin.val r
  change u.val-12=v.val-12 at t
  exact Fin.ext (by omega)

#print axioms off_five_tail_relabel_inj
open OffFive16DisconnectedSingle in
private theorem off_five_disconnected_single_marks
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (xo : x∉p.support) {j : ℕ} (h1 : 1∈Pins p x) (hj : j∈Pins p x) (jlo : 4≤j)
    (holes : j≠9 → 1∉LeftMarks p∪RightMarks p ∧ j∉LeftMarks p∪RightMarks p) :
    ∃ m : Marks, m 0=1 ∧ m 9=2 ∧
      (j≠9 → ∀ k : Fin 10,(k.val=1 ∨ k.val=j) → m k=0) ∧
      (j≠9 → ∀ k∈codeSites j,m k≠0) ∧ valid j m ∧
      (∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) := by
  classical
  have jlt := (pin_data hj).1
  have jq := pin_pos hp xo hj
  have all {k : ℕ} (nej : j≠9) (kn1 : k≠1) (knj : k≠j) (kr : k<p.length) :
      k∈LeftMarks p∪RightMarks p := by
    by_contra h
    have ht := holes nej
    have c := mark_length_ten_at_most_two_holes hp xo (p.getVert_mem_support 1) (pin_data h1).2
      ah bh len.le (i:=1) (j:=j) (k:=k) (by omega) jlt kr ht.1 ht.2 h
    omega
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support 1) (pin_data h1).2 kr h.1 h.2
  let m : Marks := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 10) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 10) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have zero (k : Fin 10) : m k=0 ↔ k.val∉LeftMarks p∪RightMarks p := by
    have kr : k.val<p.length := by have ee := k.isLt; omega
    have km : k.val∈range p.length := mem_range.mpr kr
    by_cases al : G.Adj a (p.getVert (k.val+1)) <;>
      by_cases br : G.Adj b (p.getVert k.val) <;> simp [m,al,br,LeftMarks,RightMarks,km]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m9 : m 9=2 := (r 9).mpr (by
    have rr := (p.adj_getVert_succ (i:=9) (by omega)).symm
    rw [show 9+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  have H : j≠9 → ∀ k : Fin 10,(k.val=1 ∨ k.val=j) → m k=0 := by
    intro n k kf
    apply (zero k).mpr
    rcases kf with f|f
    · exact f.symm ▸ (holes n).1
    · exact f.symm ▸ (holes n).2
  have N : j≠9 → ∀ k∈codeSites j,m k≠0 := by
    intro nn k km h
    have ki := of_decide_eq_true (List.mem_filter.mp km).2
    exact (zero k).mp h (all nn ((ki.2.2.resolve_left nn).1) ((ki.2.2.resolve_left nn).2)
      (by have z := k.isLt; omega))
  have countL : count m 1=G.degree a := by
    unfold count
    let N := univ.filter (fun k : Fin 10 => m k=1)
    have eq : N.image Fin.val=LeftMarks p := by
      ext n
      constructor
      · rintro H
        obtain ⟨k,km,rfl⟩ := mem_image.mp H
        exact mem_filter.mpr ⟨mem_range.mpr (by have g := k.isLt; omega), (l k).mp (mem_filter.mp km).2⟩
      · intro nm
        have nb := mem_range.mp (mem_filter.mp nm).1
        exact mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,(l ⟨n,by omega⟩).mpr (mem_filter.mp nm).2⟩,rfl⟩
    have ce : (N.image Fin.val).card=N.card := card_image_iff.mpr (fun _ _ _ _ e => Fin.ext e)
    change N.card=G.degree a
    rw [←ce,eq,card_leftMarks hp]
  have countR : count m 2=G.degree b := by
    unfold count
    let N := univ.filter (fun k : Fin 10 => m k=2)
    have eq : N.image Fin.val=RightMarks p := by
      ext n
      constructor
      · rintro H
        obtain ⟨k,km,rfl⟩ := mem_image.mp H
        exact mem_filter.mpr ⟨mem_range.mpr (by have g := k.isLt; omega),(r k).mp (mem_filter.mp km).2⟩
      · intro nm
        have nb := mem_range.mp (mem_filter.mp nm).1
        exact mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,(r ⟨n,by omega⟩).mpr (mem_filter.mp nm).2⟩,rfl⟩
    have ce : (N.image Fin.val).card=N.card := card_image_iff.mpr (fun _ _ _ _ e => Fin.ext e)
    change N.card=G.degree b
    rw [←ce,eq,card_rightMarks hp]

  have n1 : m 1≠1 := fun h => start_not_adj_pin_successor hp xo h1 ((l 1).mp h)
  have jv : (Fin.ofNat' 10 j).val=j := Nat.mod_eq_of_lt (by omega)
  have pv : (Fin.ofNat' 10 (j-1)).val=j-1 := Nat.mod_eq_of_lt (by omega)
  have n2 : m (Fin.ofNat' 10 j)≠1 := by
    intro h
    have f := (l (Fin.ofNat' 10 j)).mp h
    rw [jv] at f
    exact start_not_adj_pin_successor hp xo hj f
  have n3 : m (Fin.ofNat' 10 (j-1))≠2 := by
    intro h
    have f := (r (Fin.ofNat' 10 (j-1))).mp h
    rw [pv] at f
    exact end_not_adj_pin_predecessor hp xo hj f
  exact ⟨m,m0,m9,H,N,⟨countL.symm ▸ ah,countR.symm ▸ bh,n1,n2,n3⟩,l,r⟩

#print axioms off_five_disconnected_single_marks

open OffFive16DisconnectedSingle in
theorem off_five_disconnected_single_labeling
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (h4 : H.vertices.card=4) (high : ∀ z∈H.vertices,4≤G.degree z)
    (xo : x∉p.support) (xh : x∉H.vertices) (whole : ∀ z∉p.support,z=x ∨ z∈H.vertices)
    (isol : ∀ z∉p.support,¬G.Adj x z)
    (few : ∀ z∈H.vertices,(Pins p z).card≤1)
    {j : ℕ} (x1 : 1∈Pins p x) (xj : j∈Pins p x) (jlo : 4≤j) :
    ∃ (φ : Fin 16→V) (P : Tuple), Function.Injective φ ∧ Function.Surjective φ ∧ φ 11=x ∧
      (∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val) ∧
      (∀ k : Fin 16,12≤k.val → φ k∈H.vertices) ∧
      (∀ k : Fin 16,12≤k.val → Pins p (φ k)=({port P k.val}:Finset ℕ)) ∧
      (∀ u∈H.vertices,∀ v∈H.vertices,u≠v → G.Adj u v) ∧
      P∈tuples j := by
  classical
  have jt := (pin_data xj).1
  have pathOnly := (two_pin_flanks_path_only hc even conn degree hp ah bh xo x1 xj (by omega)).1
  have existsPin (z : V) (zh : z∈H.vertices) : ∃ r : ℕ, Pins p z=({r}:Finset ℕ) := by
    have bd := omitted_degree_component_bound hp.1 H zh
    have hz := high z zh
    obtain ⟨r,rp⟩ := card_pos.mp (show 0<(Pins p z).card by omega)
    have sub : ({r}:Finset ℕ)⊆Pins p z := by simpa using rp
    exact ⟨r,(eq_of_subset_of_card_le sub (by simpa using few z zh)).symm⟩
  have clique (z : V) (zh : z∈H.vertices) (w : V) (wh : w∈H.vertices) (zw : z≠w) : G.Adj z w := by
    obtain ⟨r,rp⟩ := existsPin z zh
    exact (one_port_high_complete_in_four hp.1 H h4 zh (high z zh) (r:=r) (by simp [rp])).2 w wh zw.symm
  have dis {z : V} (zh : z∈H.vertices) {r : ℕ} (rp : r∈Pins p z) (rx : r∈Pins p x) : False := by
    have zo := H.off z zh
    exact zo (pathOnly z (mem_distanceTwo.mpr
      (dist_two hc (fun e => xh (e.symm ▸ zh)) (isol z zo) (pin_data rx).2 (pin_data rp).2.symm)))
  obtain ⟨y,yh⟩ := H.nonempty
  obtain ⟨θ,injθ,surθ,atx,_,onP,offP⟩ :=
    order_sixteen_five_off_labeling hp.1 len off xo (H.off y yh) (fun e => xh (e.symm ▸ yh))
  have inside (k : Fin 16) (kl : 12≤k.val) : θ k∈H.vertices := by
    apply (whole _ (offP k (by omega))).resolve_left
    intro ex
    have ne := congrArg Fin.val (injθ (ex.trans atx.symm))
    change k.val=11 at ne
    omega
  have fi (k : Fin 4) : θ (off_five_tail_four k)∈H.vertices :=
    inside _ (by change 12≤12+k.val; omega)
  let f : Fin 4→ℕ := fun k => (existsPin _ (fi k)).choose
  have fp (k : Fin 4) : Pins p (θ (off_five_tail_four k))=({f k}:Finset ℕ) :=
    (existsPin _ (fi k)).choose_spec
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
  have face (k : Fin 16) (kl : 12≤k.val) : φ k∈H.vertices := by
    obtain ⟨i,rfl⟩ := repr k kl
    rw [eq]
    exact fi _
  let P : Tuple := (f (σ 0),f (σ 1),f (σ 2),f (σ 3))
  have pt (i : Fin 4) : port P (off_five_tail_four i).val=f (σ i) := by
    fin_cases i <;> rfl
  have pins (i : Fin 4) : Pins p (φ (off_five_tail_four i))=({f (σ i)}:Finset ℕ) := by
    rw [eq,fp]
  have pm (i : Fin 4) : f (σ i)∈Pins p (φ (off_five_tail_four i)) := by simp [pins]
  have admiss (i : Fin 4) : admissible j (f (σ i)) := by
    have hl := (pin_data (pm i)).1
    have hH := face (off_five_tail_four i) (by change 12≤12+i.val; omega)
    have pl := pin_pos hp.1 (H.off _ hH) (pm i)
    exact ⟨by omega,by omega,fun e => dis hH (pm i) (e.symm ▸ x1),
      fun e => dis hH (pm i) (e.symm ▸ xj)⟩
  have sep (i k : Fin 4) (ik : i≤k) : separated (f (σ i)) (f (σ k)) := by
    have le := mono ik
    by_cases eq : f (σ i)=f (σ k)
    · exact .inl eq
    apply Or.inr
    exact component_pins_spaced_four hc even conn degree hp ah bh H
      (face _ (by change 12≤12+i.val; omega)) (face _ (by change 12≤12+k.val; omega))
      (pm i) (pm k) (lt_of_le_of_ne le eq)
  have different : f (σ 0)≠f (σ 3) := by
    intro bad
    have ca := componentPins_card hp.1 H 2 conn
    have sub : componentPins H⊆({p.getVert (f (σ 0))}:Finset V) := by
      intro z zz
      obtain ⟨zp,w,wh,wz⟩ := mem_filter.mp zz
      obtain ⟨k,kw⟩ := sur w
      have kH : 12≤k.val := by
        by_cases yes : 12≤k.val
        · exact yes
        · have alt : k.val≤10 ∨ k.val=11 := by omega
          exfalso
          rcases alt with lo|e
          · exact H.off w wh (kw ▸ ((op k lo).symm ▸ p.getVert_mem_support k.val))
          · have ke : k=11 := Fin.ext e
            rw [ke,e11] at kw
            exact xh (kw.symm ▸ wh)
      obtain ⟨i,rfl⟩ := repr k kH
      have fEq : f (σ i)=f (σ 0) := by
        have l := mono (show (0:Fin 4)≤i by omega)
        have r := mono (show i≤(3:Fin 4) by have b := i.isLt; omega)
        exact le_antisymm (r.trans_eq bad.symm) l
      obtain ⟨r,rp,req⟩ := pin_of_neighbor_mem hp.1 (H.off w wh) (List.mem_toFinset.mp zp) wz
      rw [←kw,pins] at rp
      have rr := mem_singleton.mp rp
      exact mem_singleton.mpr (by rw [←fEq,←rr,req])
    have c := card_le_card sub
    rw [card_singleton] at c
    omega
  have ptup : P∈tuples j := mem_tuples (admiss 0) (admiss 1) (admiss 2) (admiss 3)
    (sep 0 1 (by decide)) (sep 1 2 (by decide)) (sep 2 3 (by decide)) different
  refine ⟨φ,P,inj,sur,e11,op,face,?_,clique,ptup⟩
  intro k kl
  obtain ⟨i,rfl⟩ := repr k kl
  rw [pt,pins]

#print axioms off_five_disconnected_single_labeling

open OffFive16DisconnectedSingle in
private theorem off_five_disconnected_single_oriented
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (h4 : H.vertices.card=4) (high : ∀ z∈H.vertices,4≤G.degree z)
    (xo : x∉p.support) (xh : x∉H.vertices) (whole : ∀ z∉p.support,z=x ∨ z∈H.vertices)
    (isol : ∀ z∉p.support,¬G.Adj x z) (few : ∀ z∈H.vertices,(Pins p z).card≤1)
    {j : ℕ} (xPins : Pins p x=({1,j}:Finset ℕ)) (jlo : 4≤j) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have x1 : 1∈Pins p x := by rw [xPins]; simp
  have xj : j∈Pins p x := by rw [xPins]; simp
  have jl := (pin_data xj).1
  have jhi : j≤9 := by omega
  have holes := (length_ten_two_pin_shape hc even conn degree hp ah bh len xo x1 xj (by omega)).2.2
  obtain ⟨m,m0,m9,hm,nz,valid,L,R⟩ :=
    off_five_disconnected_single_marks hp.1 ah bh len xo x1 xj jlo holes
  obtain ⟨φ,P,inj,sur,at11,value,inside,exactPin,clique,tuple⟩ :=
    off_five_disconnected_single_labeling hc even conn degree hp ah bh len off H h4 high xo xh whole isol few x1 xj jlo
  let ψ : Fin 12→V := fun k => φ (Fin.castLE (by decide : 12≤16) k)
  have inj12 : Function.Injective ψ := by
    intro u v h
    exact Fin.ext (congrArg (fun z : Fin 16 => z.val) (inj h))
  have val12 (k : Fin 12) (kl : k.val≤10) : ψ k=p.getVert k.val :=
    value (Fin.castLE (by decide : 12≤16) k) kl
  have x12 : ψ 11=x := at11
  have fw := off_five_single_pre_forward len jhi ψ val12 x12 x1 xj m L R
  obtain ⟨E0,E10,E11⟩ := off_five_single_pre_exact hp.1 len j ψ val12 x12 xo xPins m L R
  have cap12 (z : Fin 12) (e : ∀ v,G.Adj (ψ z) (ψ v) → edge j m z v=true) :
      (two j m z).card≤4 := model_d2_cap_any hc even (edge j m) ψ inj12 fw z e
  have sign := strictly_reduce_marks j m m0 m9 hm nz valid (cap12 0 E0) (cap12 10 E10) (cap12 11 E11)
    (fun no => allPreMixed j jlo (by omega)) allBoundary
  have portBound (k : Fin 16) (kl : 12≤k.val) : port P k.val≤9 := by
    have pin : port P k.val∈Pins p (φ k) := by rw [exactPin k kl]; simp
    have ub := (pin_data pin).1
    omega
  have offH (k : Fin 16) (kl : 12≤k.val) : φ k∉p.support :=
    H.off _ (inside k kl)
  have FW := off_five_single_core_forward H φ inj value inside clique j m P exactPin portBound fw
  have cap16 (z : Fin 16) (e : ∀ v,G.Adj (φ z) (φ v) → coreEdge j m P z v=true) :
      (coreTwo j m P z).card≤4 := model_d2_cap_any hc even (coreEdge j m P) φ inj FW z e
  have cd0 : (coreTwo j m P 0).card≤4 :=
    cap16 0 (off_five_single_core_exact_low hp.1 len φ value at11 offH isol j m P 0 (.inl rfl) E0)
  have cd10 : (coreTwo j m P 10).card≤4 :=
    cap16 10 (off_five_single_core_exact_low hp.1 len φ value at11 offH isol j m P 10 (.inr (.inl rfl)) E10)
  have cd11 : (coreTwo j m P 11).card≤4 :=
    cap16 11 (off_five_single_core_exact_low hp.1 len φ value at11 offH isol j m P 11 (.inr (.inr rfl)) E11)
  have highExact (z : Fin 16) (zl : 12≤z.val) :=
    cap16 z (off_five_single_core_exact_high hp.1 len φ value at11 P offH isol exactPin j m z zl)
  obtain ⟨l,path⟩ := pass_core_row (bothStages sign) tuple cd0 cd10 cd11
    (highExact 12 (by decide)) (highExact 13 (by decide)) (highExact 14 (by decide)) (highExact 15 (by decide))
  letI : Nonempty V := ⟨a⟩
  exact hamilton_of_labeled_chain φ inj sur l path.1 path.2.1 (path.2.2.imp FW)

#print axioms off_five_disconnected_single_oriented

/-- Order sixteen, five omitted vertices: disconnected omitted graph,
with only single-port contacts in its four-vertex component. -/
theorem traceable_if_five_off_disconnected_single
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (disc : ¬∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices)
    (none : ¬∃ y∉p.support,2≤(Pins p y).card ∧ ∃ z∉p.support,G.Adj y z) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have cap := fun v => distanceTwo_le_of_even 4 v (even v)
  have few {a b : V} {q : G.Walk a b} (opt : EdgeOptimal q)
      (z : V) (zo : z∉q.support) : (Pins q z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree opt zo).1
  obtain ⟨H,x,xo,xh,h4,high,whole⟩ := off_five_disconnected_shape degree hp.1 off (few hp) disc
  obtain ⟨xt,isolated⟩ := singleton_pins_of_off_five_disconnected conn hp.1 H xo xh whole (few hp x xo)
  have one (z : V) (zh : z∈H.vertices) : (Pins p z).card≤1 := by
    by_cases yes : (Pins p z).card≤1
    · exact yes
    exfalso
    have pos : 0<(H.vertices.erase z).card := by rw [card_erase_of_mem zh,h4]; decide
    obtain ⟨w,wm⟩ := card_pos.mp pos
    obtain ⟨wz,wh⟩ := mem_erase.mp wm
    obtain ⟨q,_,stay⟩ := H.joined z zh w wh
    obtain ⟨v,e,r,rfl⟩ := Walk.exists_eq_cons_of_ne wz.symm q
    have vh : v∈H.vertices := stay _ (by simp [r.start_mem_support])
    exact none ⟨z,H.off _ zh,by omega,v,H.off _ vh,e⟩
  obtain ⟨i,j,xi,xj,ij⟩ := two_pins_choose_ordered xt.ge
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo xi xj ij
  have ilo := pin_pos hp.1 xo xi
  have shape := (length_ten_two_pin_shape hc even conn degree hp ah bh len xo xi xj ij).1
  rcases shape with rfl|rfl
  · exact off_five_disconnected_single_oriented hc even conn degree hp ah bh len off H h4 high xo xh whole isolated
      one (off_five_pin_set_eq xt.le xi xj (by omega)) (by omega)
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
  have newWhole : ∀ z∉p.reverse.support,z=x ∨ z∈R.vertices := by
    intro u uo
    exact whole u (by simpa using uo)
  have newIsolated : ∀ z∉p.reverse.support,¬G.Adj x z := by
    intro u uo
    exact isolated u (by simpa using uo)
  have newOne (z : V) (zh : z∈R.vertices) : (Pins p.reverse z).card≤1 := by
    have oldOff := H.off z zh
    have newOff := R.off z zh
    have c := omittedDegree_eq hp.1 oldOff
    have d := omittedDegree_eq rev.1 newOff
    have agree : omittedNeighbors p.reverse z=omittedNeighbors p z := by simp [omittedNeighbors,support_reverse]
    rw [agree] at d
    have s := one z zh
    omega
  exact off_five_disconnected_single_oriented hc even conn degree rev bh ah rlen roff R h4 high xro xh
    newWhole newIsolated newOne (off_five_pin_set_eq (few rev x xro) rx1 rxi (by omega)) (by omega)

theorem traceable_if_five_off_disconnected
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (disc : ¬∃ H : OmittedComponent p,∀ z∉p.support,z∈H.vertices) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases h : ∃ z∉p.support,2≤(Pins p z).card ∧ ∃ w∉p.support,G.Adj z w
  · exact traceable_if_five_off_disconnected_mixed hc even conn degree hp ah bh len off disc h
  · exact traceable_if_five_off_disconnected_single hc even conn degree hp ah bh len off disc h

#print axioms traceable_if_five_off_disconnected_single
#print axioms traceable_if_five_off_disconnected
end Graffiti189LongestPath.TwoCut.SmallOrderFour
