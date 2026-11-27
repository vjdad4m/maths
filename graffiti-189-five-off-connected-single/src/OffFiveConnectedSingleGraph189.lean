import DisconnectedSingleGraphVerified
import OffFiveConnSinglePreTransfer189
import OffFiveConnSingleCoreBase189
import Mathlib.Data.List.Sort

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open private pin_data pin_pos pin_of_neighbor_mem reverse_pin no_endpoints dist_two mem_distanceTwo LeftMarks RightMarks card_leftMarks card_rightMarks from SmallOrderFour189
open private path_neighbor_is_pin_of_off from OffFiveMixedMarks189

noncomputable def allOmittedPins {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun k => ∃ z∉p.support,k∈Pins p z

theorem mem_allOmittedPins {a b : V} {p : G.Walk a b} {k : ℕ} :
    k∈allOmittedPins p ↔ ∃ z∉p.support,k∈Pins p z := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · rintro ⟨z,zo,km⟩
    exact mem_filter.mpr ⟨mem_range.mpr (pin_data km).1,z,zo,km⟩

theorem allOmittedPins_card_ge_two
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (H : OmittedComponent p) :
    2≤(allOmittedPins p).card := by
  classical
  have sub : componentPins H⊆(allOmittedPins p).image p.getVert := by
    intro z hz
    obtain ⟨zp,q,qH,qz⟩ := mem_filter.mp hz
    obtain ⟨i,ip,iz⟩ := pin_of_neighbor_mem hp (H.off _ qH) (List.mem_toFinset.mp zp) qz
    exact mem_image.mpr ⟨i,mem_allOmittedPins.mpr ⟨q,H.off _ qH,ip⟩,iz⟩
  exact ((componentPins_card hp H 2 conn).trans (card_le_card sub)).trans card_image_le

/-- At length ten, choose the direction with minimum omitted port at
most ten minus the maximum. -/
theorem orient_allOmittedPins
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (ne : (allOmittedPins p).Nonempty) :
    (∃ i∈allOmittedPins p,∀ k∈allOmittedPins p,i+k≤10) ∨
    (∃ i∈allOmittedPins p.reverse,∀ k∈allOmittedPins p.reverse,i+k≤10) := by
  classical
  let I := allOmittedPins p
  let i := I.min' ne
  let j := I.max' ne
  have im : i∈I := I.min'_mem ne
  have jm : j∈I := I.max'_mem ne
  by_cases ordered : i+j≤10
  · exact .inl ⟨i,im,fun k km => by have r := I.le_max' _ km; omega⟩
  right
  have rj : 10-j∈allOmittedPins p.reverse := by
    obtain ⟨x,xo,jp⟩ := mem_allOmittedPins.mp jm
    exact mem_allOmittedPins.mpr ⟨x,by simpa using xo,by simpa [len] using reverse_pin hp xo jp⟩
  refine ⟨10-j,rj,?_⟩
  intro k km
  obtain ⟨x,xo,kp⟩ := mem_allOmittedPins.mp km
  have rx : x∉p.support := by simpa using xo
  have vv : p.reverse.getVert k∈p.support := by
    simpa [support_reverse] using p.reverse.getVert_mem_support k
  obtain ⟨q,qp,qe⟩ := pin_of_neighbor_mem hp rx vv (pin_data kp).2
  have qI : q∈I := mem_allOmittedPins.mpr ⟨x,rx,qp⟩
  rw [getVert_reverse] at qe
  have qeq := hp.1.getVert_injOn (pin_data qp).1.le (Nat.sub_le _ _) qe
  have lo := I.min'_le _ qI
  have klt := (pin_data kp).1
  have jp : j<p.length := by
    obtain ⟨z,_,hz⟩ := mem_allOmittedPins.mp jm
    exact (pin_data hz).1
  rw [length_reverse] at klt
  omega

#print axioms allOmittedPins_card_ge_two
#print axioms orient_allOmittedPins

open OffFive16ConnectedSingle in
theorem endpoint_score_bound
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (m : Marks) (right : Bool) (P : List ℕ)
    {i j : ℕ} (ij : (i=0 ∧ j=10) ∨ (i=10 ∧ j=0))
    (exactOne : ∀ k≤10,G.Adj (p.getVert i) (p.getVert k) ↔ endCode m right k=true)
    (exactOther : ∀ k≤10,G.Adj (p.getVert j) (p.getVert k) ↔ endCode m (!right) k=true)
    (φ : Fin 5→V) (inj : Function.Injective φ) (om : ∀ k,φ k∉p.support)
    (portLink : ∀ k : Fin 5, P[k.val]?.getD 0≠0 → G.Adj (φ k) (p.getVert (P[k.val]?.getD 0))) :
    pathScore m right+porterScore m right P≤4 := by
  classical
  let S := (univ : Finset (Fin 9)).filter (fun k => middle m right k=true)
  let T := (univ : Finset (Fin 5)).filter (fun k => endCode m right (P[k.val]?.getD 0)=true)
  let A := S.image (fun k => p.getVert (k.val+1))
  let B := T.image φ
  let C : Finset V := if centerBoth m then {p.getVert j} else ∅
  have il : i≤10 := by rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have jl : j≤10 := by rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have im : i≤p.length := by omega
  have jm : j≤p.length := by omega
  have di {u : ℕ} (ul : u≤p.length) (un : i≠u) : p.getVert i≠p.getVert u :=
    fun e => un (hp.1.getVert_injOn im ul e)
  have sA : A⊆DistanceTwo G (p.getVert i) := by
    intro y ym
    obtain ⟨k,ks,rfl⟩ := mem_image.mp ym
    have km := (mem_filter.mp ks).2
    simp only [middle,Bool.and_eq_true,Bool.or_eq_true] at km
    have n := k.isLt
    have no : ¬G.Adj (p.getVert i) (p.getVert (k.val+1)) := by
      intro a
      have r := (exactOne _ (by omega)).mp a
      rw [r] at km
      exact Bool.false_ne_true km.1
    have ne : i≠k.val+1 := by rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
    apply mem_distanceTwo.mpr
    rcases km.2 with l|r
    · exact dist_two hc (di (by omega) ne) no ((exactOne _ (by omega)).mpr l)
        (p.adj_getVert_succ (i:=k.val) (by omega))
    · exact dist_two hc (di (by omega) ne) no ((exactOne _ (by omega)).mpr r)
        (p.adj_getVert_succ (i:=k.val+1) (by omega)).symm
  have sB : B⊆DistanceTwo G (p.getVert i) := by
    intro y ym
    obtain ⟨k,kt,rfl⟩ := mem_image.mp ym
    have yes := (mem_filter.mp kt).2
    let r := P[k.val]?.getD 0
    have hr : 1≤r ∧ r≤9 := by
      by_contra no
      have f : endCode m right r=false := by simp [endCode,no]
      exact Bool.false_ne_true (f.symm.trans yes)
    have ni : ¬G.Adj (p.getVert i) (φ k) := by
      have he : p.getVert i=a ∨ p.getVert i=b := by
        rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact .inl p.getVert_zero
        · exact .inr (by rw [←len,p.getVert_length])
      rcases he with h|h
      · intro e
        exact (no_endpoints hp (om k)).1 (h ▸ e.symm)
      · intro e
        exact (no_endpoints hp (om k)).2 (h ▸ e.symm)
    exact mem_distanceTwo.mpr (dist_two hc (fun e => om k (e ▸ p.getVert_mem_support i)) ni
      ((exactOne _ (by omega)).mpr yes) (portLink k (by omega)).symm)
  have sC : C⊆DistanceTwo G (p.getVert i) := by
    intro y ym
    by_cases hcM : centerBoth m=true
    · have ej : y=p.getVert j := by simpa [C,hcM] using ym
      subst y
      obtain ⟨k,km,h⟩ := List.any_eq_true.mp hcM
      simp only [Bool.and_eq_true] at h
      have kk := List.mem_range'_1.mp km
      have nen : i≠j := by rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
      have na : ¬G.Adj (p.getVert i) (p.getVert j) := by
        intro a
        have r := (exactOne j jl).mp a
        have no : ¬(1≤j ∧ j≤9) := by rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
        simp [endCode,no] at r
      have e1 : endCode m right k=true := by cases right <;> first | exact h.1 | exact h.2
      have e2 : endCode m (!right) k=true := by cases right <;> first | exact h.1 | exact h.2
      exact mem_distanceTwo.mpr (dist_two hc (di jm nen) na
        ((exactOne _ (by omega)).mpr e1) ((exactOther _ (by omega)).mpr e2).symm)
    · simp [C,hcM] at ym
  have mA (v : V) (va : v∈A) : v∈p.support := by
    obtain ⟨k,_,rfl⟩ := mem_image.mp va
    exact p.getVert_mem_support _
  have mB (v : V) (vb : v∈B) : v∉p.support := by
    obtain ⟨k,_,rfl⟩ := mem_image.mp vb
    exact om k
  have mC (v : V) (vc : v∈C) : v=p.getVert j := by
    by_cases hc : centerBoth m=true <;> simp [C,hc] at vc <;> assumption
  have disAB : Disjoint A B :=
    disjoint_left.mpr (fun v va vb => mB v vb (mA v va))
  have disC : Disjoint (A∪B) C := disjoint_left.mpr (by
    intro v vm vc
    have hv := mC v vc
    rcases mem_union.mp vm with aa|bb
    · obtain ⟨k,_,eq⟩ := mem_image.mp aa
      have e := hp.1.getVert_injOn (show k.val+1≤p.length by have klt := k.isLt; omega)
        jm (eq.trans hv)
      rcases ij with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
    · exact mB v bb (hv.symm ▸ p.getVert_mem_support j))
  have aC : A.card=S.card := card_image_iff.mpr (by
    intro u _ v _ eq
    have h := hp.1.getVert_injOn (show u.val+1≤p.length by have h := u.isLt; omega)
      (show v.val+1≤p.length by have h := v.isLt; omega) eq
    exact Fin.ext (by omega))
  have bC : B.card=T.card := card_image_of_injective _ inj
  have cC : C.card=(if centerBoth m then 1 else 0) := by
    by_cases hc : centerBoth m=true <;> simp [C,hc]
  have b := card_le_card (union_subset (union_subset sA sB) sC)
  rw [card_union_of_disjoint disC,card_union_of_disjoint disAB,aC,bC,cC] at b
  have bound := distanceTwo_le_of_even 4 (p.getVert i) (even _)
  change S.card+(if centerBoth m then 1 else 0)+T.card≤4
  omega

#print axioms endpoint_score_bound

open OffFive16ConnectedSingle in
theorem normalized_connected_single_support
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (H : OmittedComponent p) (whole : ∀ z∉p.support,z∈H.vertices)
    (orient : ∃ i∈allOmittedPins p,∀ k∈allOmittedPins p,i+k≤10) :
    ∃ S : List ℕ,S∈supportRows ∧ (∀ k,k∈S ↔ k∈allOmittedPins p) := by
  classical
  let I := allOmittedPins p
  let L := I.toList.mergeSort (fun u v => decide (u≤v))
  have perm : L.Perm I.toList := List.mergeSort_perm _ _
  have lm (k : ℕ) : k∈L ↔ k∈I := perm.mem_iff.trans Finset.mem_toList
  have size : 2≤L.length := by
    rw [perm.length_eq,Finset.length_toList]
    exact allOmittedPins_card_ge_two conn hp.1 H
  have nd : L.Nodup := perm.nodup_iff.mpr (Finset.nodup_toList _)
  have sorted : L.Pairwise (·≤·) := by
    have T (a b c : ℕ) (h : decide (a≤b)=true) (k : decide (b≤c)=true) :
        decide (a≤c)=true :=
      decide_eq_true (le_trans (of_decide_eq_true h) (of_decide_eq_true k))
    have A (a b : ℕ) : decide (a≤b) || decide (b≤a) := by simp [le_total]
    simpa using List.sorted_mergeSort T A I.toList
  have strict : L.Pairwise (fun i j => i+3≤j) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    have le := List.pairwise_iff_getElem.mp sorted i j hi hj ij
    have ne : L[i]≠L[j] := fun e => (Nat.ne_of_lt ij) (nd.getElem_inj_iff.mp e)
    obtain ⟨x,xo,xp⟩ := mem_allOmittedPins.mp ((lm _).mp (List.getElem_mem hi))
    obtain ⟨y,yo,yp⟩ := mem_allOmittedPins.mp ((lm _).mp (List.getElem_mem hj))
    exact component_pins_spaced_four hc even conn degree hp ah bh H (whole x xo) (whole y yo)
      xp yp (lt_of_le_of_ne le ne)
  have rangeL (k : ℕ) (kl : k∈L) : 1≤k ∧ k≤9 := by
    obtain ⟨x,xo,xp⟩ := mem_allOmittedPins.mp ((lm _).mp kl)
    have lo := pin_pos hp.1 xo xp
    have hi := (pin_data xp).1
    omega
  obtain ⟨i,im,check⟩ := orient
  have head : L.headD 0≤i := by
    have ink : i∈L := (lm _).mpr im
    rcases e : L with _|⟨h,t⟩
    · simp [e] at ink
    simp only [e] at ink sorted
    change h≤i
    rcases List.mem_cons.mp ink with e|e
    · exact e.ge
    · exact (List.pairwise_cons.mp sorted).1 _ e
  have ord (k : ℕ) (hk : k∈L) : L.headD 0+k≤10 :=
    (Nat.add_le_add_right head _).trans (check k ((lm _).mp hk))
  exact ⟨L,allowed_support L size strict rangeL ord,lm⟩

#print axioms normalized_connected_single_support

private def off_five_tail_five (i : Fin 5) : Fin 16 :=
  ⟨11+i.val,by have h := i.isLt; omega⟩

private def off_five_all_tail_relabel (σ : Equiv.Perm (Fin 5)) (v : Fin 16) : Fin 16 :=
  if h : v.val<11 then v else
    off_five_tail_five (σ ⟨v.val-11,by have k := v.isLt; omega⟩)

private theorem off_five_all_tail_relabel_low (σ : Equiv.Perm (Fin 5)) (v : Fin 16)
    (h : v.val<11) : off_five_all_tail_relabel σ v=v := by simp [off_five_all_tail_relabel,h]

private theorem off_five_all_tail_relabel_tail (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    off_five_all_tail_relabel σ (off_five_tail_five i)=off_five_tail_five (σ i) := by
  have no : ¬(off_five_tail_five i).val<11 := by change ¬(11+i.val<11); omega
  unfold off_five_all_tail_relabel
  rw [dif_neg no]
  congr 2
  exact Fin.ext (by change 11+i.val-11=i.val; omega)

private theorem off_five_all_tail_relabel_inj (σ : Equiv.Perm (Fin 5)) :
    Function.Injective (off_five_all_tail_relabel σ) := by
  intro u v h
  by_cases ul : u.val<11 <;> by_cases vl : v.val<11
  · rwa [off_five_all_tail_relabel_low _ _ ul,off_five_all_tail_relabel_low _ _ vl] at h
  · rw [off_five_all_tail_relabel_low _ _ ul,off_five_all_tail_relabel,dif_neg vl] at h
    have q := congrArg Fin.val h
    change u.val=11+(σ ⟨v.val-11,by have vv := v.isLt; omega⟩).val at q
    omega
  · rw [off_five_all_tail_relabel_low _ _ vl,off_five_all_tail_relabel,dif_neg ul] at h
    have q := congrArg Fin.val h
    change 11+(σ ⟨u.val-11,by have uu := u.isLt; omega⟩).val=v.val at q
    omega
  rw [off_five_all_tail_relabel,off_five_all_tail_relabel,dif_neg ul,dif_neg vl] at h
  have q := congrArg Fin.val h
  change 11+(σ ⟨u.val-11,by have uu := u.isLt; omega⟩).val=
    11+(σ ⟨v.val-11,by have vv := v.isLt; omega⟩).val at q
  have r := σ.injective (Fin.ext (show
    (σ ⟨u.val-11,by have uu := u.isLt; omega⟩).val =
    (σ ⟨v.val-11,by have vv := v.isLt; omega⟩).val by omega))
  have t := congrArg Fin.val r
  change u.val-11=v.val-11 at t
  exact Fin.ext (by omega)

#print axioms off_five_all_tail_relabel_inj

open OffFive16ConnectedSingle in
theorem off_five_connected_single_labeling
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (whole : ∀ z∉p.support,z∈H.vertices)
    (few : ∀ z∉p.support,(Pins p z).card≤1)
    (S : List ℕ) (signS : ∀ k,k∈S ↔ k∈allOmittedPins p) :
    ∃ (φ : Fin 16→V) (P : List ℕ), Function.Injective φ ∧ Function.Surjective φ ∧
      (∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val) ∧
      (∀ k : Fin 16,11≤k.val → φ k∈H.vertices) ∧
      (∀ k : Fin 16,11≤k.val → ∀ r,r∈Pins p (φ k) ↔ r=pin P k.val ∧ r≠0) ∧
      P.length=5 ∧ P∈tuples S := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have oc : O.card=5 := off
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  obtain ⟨x,xO,y,yO,xy⟩ := one_lt_card.mp (show 1<O.card by omega)
  obtain ⟨θ,injθ,surθ,_,_,onP,offP⟩ :=
    order_sixteen_five_off_labeling hp len off (out.mp xO) (out.mp yO) xy
  have lc (i : Fin 5) : 11≤(off_five_tail_five i).val := by change 11≤11+i.val; omega
  let f : Fin 5→ℕ := fun k =>
    if n : (Pins p (θ (off_five_tail_five k))).Nonempty then (Pins p (θ (off_five_tail_five k))).min' n else 0
  have fp (k : Fin 5) (r : ℕ) : r∈Pins p (θ (off_five_tail_five k)) ↔ r=f k ∧ r≠0 := by
    have ko := offP _ (lc k)
    by_cases n : (Pins p (θ (off_five_tail_five k))).Nonempty
    · have fm : f k∈Pins p (θ (off_five_tail_five k)) := by
        dsimp [f]
        rw [dif_pos n]
        exact min'_mem _ _
      have nz := Nat.ne_of_gt (pin_pos hp ko fm)
      constructor
      · intro rr
        have eq : r=f k := by
          by_contra e
          have c := one_lt_card.mpr ⟨r,rr,f k,fm,e⟩
          exact (Nat.not_lt_of_ge (few _ ko)) c
        exact ⟨eq,eq.symm ▸ nz⟩
      · rintro ⟨rfl,_⟩
        exact fm
    · have z : f k=0 := by simp [f,n]
      constructor
      · exact fun h => (n ⟨r,h⟩).elim
      · exact fun h => (h.2 (h.1.trans z)).elim
  obtain ⟨σ,mono⟩ := exists_mono_perm_fin f
  let φ : Fin 16→V := θ ∘ off_five_all_tail_relabel σ
  have eq (k : Fin 5) : φ (off_five_tail_five k)=θ (off_five_tail_five (σ k)) := by
    simp [φ,off_five_all_tail_relabel_tail]
  have inj : Function.Injective φ := injθ.comp (off_five_all_tail_relabel_inj σ)
  have sur : Function.Surjective φ := surθ.comp (Finite.surjective_of_injective (off_five_all_tail_relabel_inj σ))
  have op (k : Fin 16) (kl : k.val≤10) : φ k=p.getVert k.val := by
    change θ (off_five_all_tail_relabel σ k)=p.getVert k.val
    rw [off_five_all_tail_relabel_low _ _ (by omega)]
    exact onP k kl
  have repr (k : Fin 16) (kl : 11≤k.val) : ∃ i : Fin 5,k=off_five_tail_five i := by
    refine ⟨⟨k.val-11,by have h := k.isLt; omega⟩,Fin.ext ?_⟩
    change k.val=11+(k.val-11)
    omega
  have inside (k : Fin 16) (kl : 11≤k.val) : φ k∈H.vertices := by
    obtain ⟨i,rfl⟩ := repr k kl
    rw [eq]
    exact whole _ (offP _ (lc (σ i)))
  let P := List.ofFn (fun i : Fin 5 => f (σ i))
  have lenP : P.length=5 := by simp [P]
  have val (i : Fin 5) : pin P (off_five_tail_five i).val=f (σ i) := by
    have e : (off_five_tail_five i).val-11=i.val := by change 11+i.val-11=i.val; omega
    rw [pin,e]
    simp only [P,List.getElem?_ofFn,i.isLt,dif_pos,Option.getD_some]
  have pins (k : Fin 16) (kl : 11≤k.val) (r : ℕ) :
      r∈Pins p (φ k) ↔ r=pin P k.val ∧ r≠0 := by
    obtain ⟨i,rfl⟩ := repr k kl
    rw [val,eq]
    exact fp _ _
  have allP (k : ℕ) (kp : k∈P) : k=0 ∨ k∈S := by
    by_cases ne : k=0
    · exact .inl ne
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp kp
    let z := off_five_tail_five i
    have e : f (σ i)∈Pins p (φ z) := by
      apply (pins z (by change 11≤11+i.val; omega) _).mpr
      rw [val]
      exact ⟨rfl,ne⟩
    exact .inr ((signS _).mpr (mem_allOmittedPins.mpr ⟨φ z,H.off _ (inside z (by change 11≤11+i.val; omega)),e⟩))
  have allS (k : ℕ) (ks : k∈S) : k∈P := by
    obtain ⟨z,zo,kp⟩ := mem_allOmittedPins.mp ((signS _).mp ks)
    obtain ⟨u,uz⟩ := sur z
    have ul : 11≤u.val := by
      by_cases yes : 11≤u.val
      · exact yes
      exact False.elim (zo (uz ▸ ((op u (by omega)).symm ▸ p.getVert_mem_support u.val)))
    have e := (pins u ul k).mp (uz.symm ▸ kp)
    obtain ⟨i,rfl⟩ := repr u ul
    rw [val] at e
    rw [e.1]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have sorted : P.Pairwise (·≤·) := List.pairwise_ofFn.mpr (fun _ _ ij => mono ij.le)
  exact ⟨φ,P,inj,sur,op,inside,pins,lenP,mem_tuples lenP allP sorted allS⟩

#print axioms off_five_connected_single_labeling

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_marks
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (S : List ℕ) (signS : ∀ k,k∈S ↔ k∈allOmittedPins p)
    (ne : (allOmittedPins p).Nonempty) :
    ∃ m : Marks,m 0=1 ∧ m 9=2 ∧ 4≤count m 1 ∧ 4≤count m 2 ∧
      (∀ k∈S,m (Fin.ofNat' 10 k)≠1 ∧ m (Fin.ofNat' 10 (k-1))≠2) ∧
      (∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) := by
  classical
  obtain ⟨k0,km⟩ := ne
  obtain ⟨x,xo,xp⟩ := mem_allOmittedPins.mp km
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support k0) (pin_data xp).2 kr h.1 h.2
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


  have rot (k : ℕ) (ks : k∈S) : m (Fin.ofNat' 10 k)≠1 ∧ m (Fin.ofNat' 10 (k-1))≠2 := by
    obtain ⟨z,zo,zp⟩ := mem_allOmittedPins.mp ((signS k).mp ks)
    have pk := (pin_data zp).1
    have jv : (Fin.ofNat' 10 k).val=k := Nat.mod_eq_of_lt (by omega)
    have pv : (Fin.ofNat' 10 (k-1)).val=k-1 := Nat.mod_eq_of_lt (by omega)
    constructor
    · intro h
      have f := (l (Fin.ofNat' 10 k)).mp h
      rw [jv] at f
      exact start_not_adj_pin_successor hp zo zp f
    · intro h
      have f := (r (Fin.ofNat' 10 (k-1))).mp h
      rw [pv] at f
      exact end_not_adj_pin_predecessor hp zo zp f
  exact ⟨m,m0,m9,countL.symm ▸ ah,countR.symm ▸ bh,rot,l,r⟩

open OffFive16ConnectedSingle in
private theorem off_five_endpoint_codes_exact
    {a b : V} {p : G.Walk a b} (len : p.length=10)
    (m : Marks) (_m0 : m 0=1) (m9 : m 9=2)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    (∀ k≤10,G.Adj (p.getVert 0) (p.getVert k) ↔ endCode m false k=true) ∧
    (∀ k≤10,G.Adj (p.getVert 10) (p.getVert k) ↔ endCode m true k=true) := by
  have a0 : p.getVert 0=a := p.getVert_zero
  have b10 : p.getVert 10=b := by rw [←len,p.getVert_length]
  have na : ¬G.Adj a b := by
    intro e
    have hc := (L 9).mpr (show G.Adj a (p.getVert (9+1)) from b10.symm ▸ e)
    rw [m9] at hc
    exact (by decide : (2:Fin 3)≠1) hc
  have nb : ¬G.Adj b a := fun e => na e.symm
  constructor
  · intro k kl
    rw [a0]
    by_cases yes : 1≤k ∧ k≤9
    · simp only [endCode,dif_pos yes,Bool.false_eq_true,if_false,decide_eq_true_eq]
      have adj := L ⟨k-1,by omega⟩
      change m ⟨k-1,by omega⟩=1 ↔ G.Adj a (p.getVert (k-1+1)) at adj
      rw [show k-1+1=k by omega] at adj
      exact adj.symm
    have alt : k=0 ∨ k=10 := by omega
    rcases alt with rfl|rfl
    · simp [endCode,yes,a0]
    · simp [endCode,yes,b10,na]
  · intro k kl
    rw [b10]
    by_cases yes : 1≤k ∧ k≤9
    · simp only [endCode,dif_pos yes,if_true,decide_eq_true_eq]
      exact (R ⟨k,by omega⟩).symm
    have alt : k=0 ∨ k=10 := by omega
    rcases alt with rfl|rfl
    · simp [endCode,yes,a0,nb]
    · simp [endCode,yes,b10]

#print axioms off_five_connected_single_marks
#print axioms off_five_endpoint_codes_exact
open OffFive16ConnectedSingle in
private def off_five_connected_single_mask (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : Fin 16→V) : List Bool :=
  corePair.map fun q => decide
    (G.Adj (φ (Fin.ofNat' 16 q.1)) (φ (Fin.ofNat' 16 q.2)))

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_raw_bit
    (φ : Fin 16→V) {a b : ℕ} (h : (a,b)∈corePair) :
    rawBit (off_five_connected_single_mask G φ) a b =
      decide (G.Adj (φ (Fin.ofNat' 16 a)) (φ (Fin.ofNat' 16 b))) := by
  unfold rawBit off_five_connected_single_mask
  have bit : corePair[corePair.idxOf (a,b)]? = some (a,b) := by
    simp only [corePair,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h|h <;>
      have ha := congrArg Prod.fst h <;>
      have hb := congrArg Prod.snd h <;>
      simp only [Prod.fst,Prod.snd] at ha hb <;>
      subst a <;> subst b <;> decide
  rw [List.getElem?_map,bit]
  rfl

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_internal
    (φ : Fin 16→V) {u v : Fin 16} (uh : 11≤u.val) (vh : 11≤v.val) (ne : u≠v) :
    internal (off_five_connected_single_mask G φ) u.val v.val=true ↔ G.Adj (φ u) (φ v) := by
  have bit {u v : Fin 16} (ul : 11≤u.val) (uv : u.val<v.val) :
      rawBit (off_five_connected_single_mask G φ) u.val v.val=true ↔ G.Adj (φ u) (φ v) := by
    have h := v.isLt
    have p : (u.val,v.val)∈corePair := by
      have alt : (u.val=11 ∧ v.val=12) ∨ (u.val=11 ∧ v.val=13) ∨ (u.val=11 ∧ v.val=14) ∨ (u.val=11 ∧ v.val=15) ∨ (u.val=12 ∧ v.val=13) ∨ (u.val=12 ∧ v.val=14) ∨ (u.val=12 ∧ v.val=15) ∨ (u.val=13 ∧ v.val=14) ∨ (u.val=13 ∧ v.val=15) ∨ (u.val=14 ∧ v.val=15) := by omega
      rcases alt with ⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩|⟨h,k⟩ <;> simp [corePair,h,k]
    have ue : Fin.ofNat' 16 u.val=u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
    have ve : Fin.ofNat' 16 v.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
    rw [off_five_connected_single_raw_bit φ p,ue,ve]
    exact Iff.of_eq (@decide_eq_true_eq (G.Adj (φ u) (φ v)) _)
  have nv : u.val≠v.val := fun h => ne (Fin.ext h)
  rcases lt_or_gt_of_ne nv with uv|vu
  · rw [internal,if_pos uv]
    exact bit uh uv
  · rw [internal,if_neg (by omega : ¬u.val<v.val)]
    exact (bit vh vu).trans (G.adj_comm _ _)

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_forward
    {a b : V} {p : G.Walk a b} (len : p.length=10)
    (φ : Fin 16→V) (val : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (m : Marks) (P : List ℕ)
    (ports : ∀ k : Fin 16,11≤k.val → ∀ r,r∈Pins p (φ k) ↔ r=pin P k.val ∧ r≠0)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 10,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    ∀ u v,edge m P (off_five_connected_single_mask G φ) u v=true → G.Adj (φ u) (φ v) := by
  have direction (u v : Fin 16) (h : dirPre m P u v=true) : G.Adj (φ u) (φ v) := by
    simp only [dirPre,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with (((ha|⟨vr,hn,vh⟩)|he)|hf)
    · rw [val u (by omega),val v ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · have p := (ports v vh u.val).mpr ⟨vr,hn⟩
      have q := (pin_data p).1
      rw [val u (by omega)]
      exact (pin_data p).2.symm
    · by_cases q : u.val=0 ∧ 1≤v.val ∧ v.val≤10
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [val u (by omega),val v q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨v.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (v.val-1+1)) at h
        rwa [show v.val-1+1=v.val by omega] at h
      · simp only [dif_neg q] at he
        contradiction
    · by_cases q : v.val=10 ∧ u.val<10
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [val u (by omega),val v (by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨u.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        contradiction
  intro u v h
  simp only [edge,edgePre,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ((a|b)|⟨⟨ul,vl,ne⟩,hi⟩)
  · exact direction _ _ a
  · exact (direction _ _ b).symm
  · exact (off_five_connected_single_internal φ ul vl ne).mp hi

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_exact
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (φ : Fin 16→V) (val : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (off : ∀ k : Fin 16,11≤k.val → φ k∉p.support)
    (m : Marks) (P : List ℕ)
    (ports : ∀ k : Fin 16,11≤k.val → ∀ r,r∈Pins p (φ k) ↔ r=pin P k.val ∧ r≠0)
    (u : Fin 16) (ul : 11≤u.val) :
    ∀ v,G.Adj (φ u) (φ v) → edge m P (off_five_connected_single_mask G φ) u v=true := by
  intro v e
  by_cases vl : 11≤v.val
  · have ne : u≠v := fun h => G.loopless _ (h ▸ e)
    simp only [edge,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    exact .inr ⟨⟨ul,vl,ne⟩,(off_five_connected_single_internal φ ul vl ne).mpr e⟩
  have pi := path_neighbor_is_pin_of_off hp (off u ul) (show v.val≤p.length by omega)
    (by rwa [←val v (by omega)])
  have port := (ports u ul _).mp pi
  simp only [edge,edgePre,dirPre,Bool.or_eq_true,decide_eq_true_eq]
  exact .inl (.inr (.inl (.inl (.inr ⟨port.1,port.2,ul⟩))))

#print axioms off_five_connected_single_internal
#print axioms off_five_connected_single_forward
#print axioms off_five_connected_single_exact

private theorem five_distance_two_impossible (x : V) (f : Fin 5 → V)
    (inj : Function.Injective f) (mem : ∀ i, f i ∈ DistanceTwo G x)
    (cap : (DistanceTwo G x).card ≤ 4) : False := by
  have sub : (Finset.univ.image f : Finset V) ⊆ DistanceTwo G x := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact mem i
  have e := (Finset.card_le_card sub).trans cap
  rw [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin] at e
  omega

open OffFive16ConnectedSingle in
private theorem off_five_core_label_count (F : ℕ → Bool) :
    (coreLabels.filter F).length =
      ((Finset.univ : Finset (Fin 16)).filter (fun v => 11≤v.val ∧ F v.val=true)).card := by
  let A := (Finset.univ : Finset (Fin 16)).filter (fun v => 11≤v.val ∧ F v.val=true)
  have eq : A.image Fin.val = (coreLabels.filter F).toFinset := by
    ext b
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨u,⟨low,good⟩,rfl⟩
      refine ⟨?_,good⟩
      have h := u.isLt
      simp only [coreLabels,List.mem_cons,List.not_mem_nil,or_false]
      omega
    · rintro ⟨ran,good⟩
      have h : 11≤b ∧ b<16 := by
        simp only [coreLabels,List.mem_cons,List.not_mem_nil,or_false] at ran
        omega
      exact ⟨⟨b,h.2⟩,⟨h.1,good⟩,rfl⟩
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (by decide : coreLabels.Nodup)), ←eq]
  exact Finset.card_image_of_injective _ (fun a b h => Fin.ext h)

open private omittedDegree_eq omittedNeighbors from FourOffGraphCore189

open OffFive16ConnectedSingle in
private theorem off_five_core_degree_exact
    {a b : V} {p : G.Walk a b} (φ : Fin 16 → V)
    (inj : Function.Injective φ) (sur : Function.Surjective φ)
    (val : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (off : ∀ k : Fin 16,11≤k.val → φ k∉p.support)
    (u : Fin 16) (ul : 11≤u.val) :
    coreDeg (off_five_connected_single_mask G φ) u.val=(omittedNeighbors p (φ u)).card := by
  classical
  let M := off_five_connected_single_mask G φ
  let S := (Finset.univ : Finset (Fin 16)).filter
    (fun v => 11≤v.val ∧ (decide (u.val≠v.val) && internal M u.val v.val)=true)
  have h : S.image φ = omittedNeighbors p (φ u) := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,vm,rfl⟩ := Finset.mem_image.mp hx
      have hv := (Finset.mem_filter.mp vm).2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hv
      have ne : u≠v := fun q => hv.2.1 (congrArg Fin.val q)
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((off_five_connected_single_internal φ ul hv.1 ne).mp hv.2.2),off v hv.1⟩
    · intro hx
      obtain ⟨v,rfl⟩ := sur x
      have no := (Finset.mem_filter.mp hx).2
      have va := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).1
      have vl : 11≤v.val := by
        by_contra! vv
        exact no (val v (by omega) ▸ p.getVert_mem_support v.val)
      have ne : u≠v := fun e => G.loopless _ (e ▸ va)
      have nv : u.val≠v.val := fun e => ne (Fin.ext e)
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,vl,
        Bool.and_eq_true_iff.mpr ⟨decide_eq_true nv,
          (off_five_connected_single_internal φ ul vl ne).mpr va⟩⟩,rfl⟩
  rw [coreDeg,off_five_core_label_count,←h]
  exact (Finset.card_image_of_injective _ inj).symm

open OffFive16ConnectedSingle in
private theorem off_five_core_degree_gate
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (φ : Fin 16 → V) (inj : Function.Injective φ) (sur : Function.Surjective φ)
    (val : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (off : ∀ k : Fin 16,11≤k.val → φ k∉p.support)
    (single : ∀ x∉p.support,(Pins p x).card≤1)
    (P : List ℕ)
    (ports : ∀ k : Fin 16,11≤k.val → ∀ r,r∈Pins p (φ k) ↔ r=pin P k.val ∧ r≠0)
    (nonempty : ∀ x∉p.support, (omittedNeighbors p x).Nonempty)
    (degree : ((Finset.univ : Finset V).filter (fun v => G.degree v<4)).card≤1) :
    gateDegree P (off_five_connected_single_mask G φ)=true := by
  classical
  let M := off_five_connected_single_mask G φ
  have range : ∀ k∈coreLabels, 11≤k ∧ k<16 := by
    intro k hk
    simp only [coreLabels,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have valid (k : ℕ) (low : 11≤k) (hi : k<16) :
      coreDeg M k=(omittedNeighbors p (φ ⟨k,hi⟩)).card :=
    off_five_core_degree_exact φ inj sur val off ⟨k,hi⟩ low
  unfold gateDegree
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨?_,?_⟩
  · intro k hk
    obtain ⟨low,hi⟩ := range k hk
    rw [valid k low hi]
    exact Finset.card_pos.mpr (nonempty _ (off _ low))
  · rw [off_five_core_label_count]
    let S := (Finset.univ : Finset (Fin 16)).filter
      (fun v => 11≤v.val ∧ decide (coreDeg M v.val+(if pin P v.val=0 then 0 else 1)<4)=true)
    have sub : S.image φ ⊆ (Finset.univ : Finset V).filter (fun v => G.degree v<4) := by
      intro v hv
      obtain ⟨u,um,rfl⟩ := Finset.mem_image.mp hv
      have h := (Finset.mem_filter.mp um).2
      have e := (off_five_core_degree_exact φ inj sur val off u h.1)
      have dn := omittedDegree_eq hp (off u h.1)
      have pn := single _ (off u h.1)
      have pc : (Pins p (φ u)).card = (if pin P u.val=0 then 0 else 1) := by
        by_cases yes : pin P u.val=0
        · have none : Pins p (φ u)=∅ := by
            ext k
            simp [ports u h.1,yes]
          simp [yes,none]
        · have pm := (ports u h.1 _).mpr ⟨rfl,yes⟩
          have ppos := card_pos.mpr ⟨_,pm⟩
          simp only [if_neg yes]
          omega
      rcases h with ⟨_,h⟩
      simp only [decide_eq_true_eq, M] at h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have d := (Finset.card_le_card sub).trans degree
    rwa [Finset.card_image_of_injective _ inj] at d

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_exception_impossible
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (hc : G.Connected) (cap : ∀ x,(DistanceTwo G x).card≤4)
    (φ : Fin 16→V) (inj : Function.Injective φ)
    (val : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (off : ∀ k : Fin 16,11≤k.val → φ k∉p.support)
    (m : Marks) (P : List ℕ)
    (ports : ∀ k : Fin 16,11≤k.val → ∀ r,r∈Pins p (φ k) ↔ r=pin P k.val ∧ r≠0)
    (L : ∀ k : Fin 10,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (ex : exceptional m P (off_five_connected_single_mask G φ)) : False := by
  classical
  obtain ⟨rfl,signs,mask⟩ := ex
  have nPort (k r : Fin 16) (kl : 11≤k.val) (rl : r.val≤10)
      (neq : r.val≠pin [0,0,0,3,7] k.val) : ¬G.Adj (φ k) (φ r) := by
    intro adj
    have q := (pin_of_neighbor_mem hp (off k kl) (p.getVert_mem_support r.val)
      (val r rl ▸ adj))
    obtain ⟨i,hi,eq⟩ := q
    have rlen : r.val≤p.length := by omega
    have ir := (pin_data hi).1
    have ep := hp.1.getVert_injOn (show i∈Set.Iic p.length from ir.le)
      (show r.val∈Set.Iic p.length from rlen) eq
    exact neq (ep ▸ ((ports k kl i).mp hi).1)
  have attach (k r : Fin 16) (kl : 11≤k.val) (rl : r.val≤10)
      (eq : r.val=pin [0,0,0,3,7] k.val) (nz : r.val≠0) : G.Adj (φ k) (φ r) := by
    rw [val r rl]
    exact (pin_data ((ports k kl r.val).mpr ⟨eq,nz⟩)).2
  have step (u v : Fin 16) (uv : u.val+1=v.val) (vl : v.val≤10) : G.Adj (φ u) (φ v) := by
    rw [val u (by omega),val v vl,←uv]
    exact p.adj_getVert_succ (by omega)
  have c03 : G.Adj (φ 0) (φ 3) := by
    have h := congrArg (fun l : List (Fin 3) => l[2]?) signs
    simp only [List.getElem?_ofFn] at h
    have h2 : m 2=1 := by
      simpa using h
    rw [val 0 (by decide),val 3 (by decide)]
    change G.Adj (p.getVert 0) (p.getVert 3)
    rw [p.getVert_zero]
    exact (L 2).mp h2
  have c143 : G.Adj (φ 14) (φ 3) := attach 14 3 (by decide) (by decide) (by decide) (by decide)
  have c157 : G.Adj (φ 15) (φ 7) := attach 15 7 (by decide) (by decide) (by decide) (by decide)
  have step2 (u v w : Fin 16) (ne : v≠u) (no : ¬G.Adj (φ u) (φ v))
      (e : G.Adj (φ u) (φ w)) (f : G.Adj (φ w) (φ v)) : φ v∈DistanceTwo G (φ u) :=
    mem_distanceTwo.mpr (dist_two hc (fun q => ne (inj q.symm)) no e f)
  have adjCore (u v : Fin 16) (ul : 11≤u.val) (vl : 11≤v.val) (ne : u≠v)
      (M : List Bool) (eq : off_five_connected_single_mask G φ=M)
      (h : internal M u.val v.val=true) : G.Adj (φ u) (φ v) :=
    (off_five_connected_single_internal φ ul vl ne).mp (eq.symm ▸ h)
  have t11 : G.Adj (φ 14) (φ 11) := by
    rcases mask with l|r <;>
      first | exact adjCore 14 11 (by decide) (by decide) (by decide) _ l (by decide)
            | exact adjCore 14 11 (by decide) (by decide) (by decide) _ r (by decide)
  have t12 : G.Adj (φ 14) (φ 12) := by
    rcases mask with l|r <;>
      first | exact adjCore 14 12 (by decide) (by decide) (by decide) _ l (by decide)
            | exact adjCore 14 12 (by decide) (by decide) (by decide) _ r (by decide)
  have t13 : G.Adj (φ 14) (φ 13) := by
    rcases mask with l|r <;>
      first | exact adjCore 14 13 (by decide) (by decide) (by decide) _ l (by decide)
            | exact adjCore 14 13 (by decide) (by decide) (by decide) _ r (by decide)
  have extra : ∃ w : Fin 16, (w=7 ∨ w=15) ∧ φ w∈DistanceTwo G (φ 14) := by
    rcases mask with l|r
    · refine ⟨15, .inr rfl, step2 14 15 11 (by decide) ?_ t11 ?_⟩
      · intro edge
        have h := (off_five_connected_single_internal φ (u:=14) (v:=15)
          (by decide) (by decide) (by decide)).mpr edge
        rw [l] at h
        contradiction
      · exact adjCore 11 15 (by decide) (by decide) (by decide) _ l (by decide)
    · exact ⟨7, .inl rfl, step2 14 7 15 (by decide)
        (nPort 14 7 (by decide) (by decide) (by decide))
        (adjCore 14 15 (by decide) (by decide) (by decide) _ r (by decide)) c157⟩
  obtain ⟨w,wt,wm⟩ := extra
  have no (k : Fin 16) (kt : k=1 ∨ k=5) : ¬G.Adj (φ 3) (φ k) := by
    intro edge
    let f : Fin 5→Fin 16 := fun i => ([0,2,4,k,w] : List (Fin 16))[i.val]'(by simp)
    have fi : Function.Injective f := by
      rcases kt with rfl|rfl <;> rcases wt with rfl|rfl <;> decide
    apply five_distance_two_impossible (φ 14) (φ ∘ f) (inj.comp fi) _ (cap _)
    intro i
    fin_cases i
    · exact step2 14 0 3 (by decide) (nPort 14 0 (by decide) (by decide) (by decide)) c143 c03.symm
    · exact step2 14 2 3 (by decide) (nPort 14 2 (by decide) (by decide) (by decide)) c143 (step 2 3 (by decide) (by decide)).symm
    · exact step2 14 4 3 (by decide) (nPort 14 4 (by decide) (by decide) (by decide)) c143 (step 3 4 (by decide) (by decide))
    · change φ k∈DistanceTwo G (φ 14)
      rcases kt with rfl|rfl <;>
        exact step2 14 _ 3 (by decide) (nPort 14 _ (by decide) (by decide) (by decide)) c143 edge
    · exact wm
  let f : Fin 5→Fin 16 := fun i => ([1,5,11,12,13] : List (Fin 16))[i.val]'(by simp)
  have fi : Function.Injective f := by decide
  apply five_distance_two_impossible (φ 3) (φ ∘ f) (inj.comp fi) _ (cap _)
  intro i
  fin_cases i
  · exact step2 3 1 2 (by decide) (no 1 (.inl rfl))
      (step 2 3 (by decide) (by decide)).symm (step 1 2 (by decide) (by decide)).symm
  · exact step2 3 5 4 (by decide) (no 5 (.inr rfl))
      (step 3 4 (by decide) (by decide)) (step 4 5 (by decide) (by decide))
  · exact step2 3 11 14 (by decide)
      (fun h => nPort 11 3 (by decide) (by decide) (by decide) h.symm) c143.symm t11
  · exact step2 3 12 14 (by decide)
      (fun h => nPort 12 3 (by decide) (by decide) (by decide) h.symm) c143.symm t12
  · exact step2 3 13 14 (by decide)
      (fun h => nPort 13 3 (by decide) (by decide) (by decide) h.symm) c143.symm t13

open private hamilton_of_labeled_chain from FourOffGraphCore189
open private model_d2_cap_any from DisconnectedSingleGraphVerified
open private same_support_optimal reverse_long from SmallOrderFour189

open OffFive16ConnectedSingle in
private theorem off_five_connected_single_oriented
    (preTable : ∀ {S : List ℕ}, S∈supportRows → preRow S=true)
    (coreTable : ∀ {S P : List ℕ} {m : Marks}, matchPre S P m=true → coreRow P (List.ofFn m)=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (whole : ∀ z∉p.support,z∈H.vertices)
    (single : ∀ z∉p.support,(Pins p z).card≤1)
    (orient : ∃ i∈allOmittedPins p,∀ k∈allOmittedPins p,i+k≤10) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  obtain ⟨S,sm,exactS⟩ := normalized_connected_single_support hc even conn degree hp ah bh len H whole orient
  obtain ⟨m,m0,m9,ml,mr,rot,L,R⟩ := off_five_connected_single_marks hp.1 ah bh len S exactS
    (card_pos.mp (by have h := allOmittedPins_card_ge_two conn hp.1 H; omega))
  obtain ⟨φ,P,inj,sur,val,inside,ports,_,pt⟩ :=
    off_five_connected_single_labeling hp.1 len off H whole single S exactS
  have offφ (k : Fin 16) (kl : 11≤k.val) := H.off _ (inside k kl)
  let ψ : Fin 5→V := fun k => φ (off_five_tail_five k)
  have ψi : Function.Injective ψ := by
    intro i j h
    have v := congrArg Fin.val (inj h)
    change 11+i.val=11+j.val at v
    exact Fin.ext (by omega)
  have ψo (k : Fin 5) : ψ k∉p.support := offφ _ (by change 11≤11+k.val; omega)
  have portLink (k : Fin 5) (hn : P[k.val]?.getD 0≠0) :
      G.Adj (ψ k) (p.getVert (P[k.val]?.getD 0)) := by
    have eq : pin P (off_five_tail_five k).val=P[k.val]?.getD 0 := by
      unfold pin
      congr 2
      change 11+k.val-11=k.val
      omega
    have pr := (ports (off_five_tail_five k) (by change 11≤11+k.val; omega) _).mpr
       ⟨eq.symm,hn⟩
    exact (pin_data pr).2
  obtain ⟨E0,E10⟩ := off_five_endpoint_codes_exact len m m0 m9 L R
  have cap0 := endpoint_score_bound hc even hp.1 len m false P (.inl ⟨rfl,rfl⟩) E0 E10 ψ ψi ψo portLink
  have cap10 := endpoint_score_bound hc even hp.1 len m true P (.inr ⟨rfl,rfl⟩) E10 E0 ψ ψi ψo portLink
  have reduced := projected_match (preTable sm) pt m0 m9 rot ml mr cap0 cap10
  have below : ((univ : Finset V).filter (fun v=>G.degree v<4)).card≤1 := by
    apply Nat.le_of_not_gt
    intro h
    obtain ⟨u,um,v,vm,ne⟩ := one_lt_card.mp h
    have q := (mem_filter.mp um).2
    have r := (mem_filter.mp vm).2
    rcases degree u v ne with h|h <;> omega
  have nonempty (z : V) (zo : z∉p.support) : (omittedNeighbors p z).Nonempty := by
    have alt : ∃ w∈H.vertices,w≠z := by
      by_cases e : φ 11=z
      · refine ⟨φ 12,inside 12 (by decide),?_⟩
        intro e'
        exact (by decide : (11 : Fin 16)≠12) (inj (e.trans e'.symm))
      · exact ⟨φ 11,inside 11 (by decide),e⟩
    obtain ⟨w,wm,wz⟩ := alt
    obtain ⟨q,_,stay⟩ := H.joined z (whole z zo) w wm
    obtain ⟨v,e,r,rfl⟩ := Walk.exists_eq_cons_of_ne wz.symm q
    have vm : v∈H.vertices := stay _ (by simp [r.start_mem_support])
    exact ⟨v,mem_filter.mpr ⟨(mem_neighborFinset G _ _).mpr e,H.off _ vm⟩⟩
  let M := off_five_connected_single_mask G φ
  have dg : gateDegree P M=true := off_five_core_degree_gate hp.1 φ inj sur val offφ single P ports nonempty below
  have ml : M.length=10 := by simp [M,off_five_connected_single_mask,corePair]
  have fw := off_five_connected_single_forward len φ val m P ports L R
  have cap (z : Fin 16) (zl : 11≤z.val) : (two m P M z).card≤4 :=
    model_d2_cap_any hc even (edge m P M) φ inj fw z
      (off_five_connected_single_exact hp.1 len φ val offφ m P ports z zl)
  have caps : caps m P M two :=
    ⟨cap 11 (by decide),cap 12 (by decide),cap 13 (by decide),cap 14 (by decide),cap 15 (by decide)⟩
  rcases row_disjunction (coreTable reduced) ml dg caps with ⟨l,h⟩|bad
  · letI : Nonempty V := ⟨a⟩
    exact hamilton_of_labeled_chain φ inj sur l h.1 h.2.1 (h.2.2.imp fw)
  · exact (off_five_connected_single_exception_impossible hp.1 len hc
      (fun x=>distanceTwo_le_of_even 4 x (even x)) φ inj val offφ m P ports L bad).elim

open OffFive16ConnectedSingle in
theorem traceable_if_five_off_connected_single_with_table
    (preTable : ∀ {S : List ℕ}, S∈supportRows → preRow S=true)
    (coreTable : ∀ {S P : List ℕ} {m : Marks}, matchPre S P m=true → coreRow P (List.ofFn m)=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (H : OmittedComponent p) (whole : ∀ z∉p.support,z∈H.vertices)
    (single : ∀ z∉p.support,(Pins p z).card≤1) :
    ∃ a b : V,∃ q : G.Walk a b,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  have large := allOmittedPins_card_ge_two conn hp.1 H
  rcases orient_allOmittedPins hp.1 len (card_pos.mp (by omega : 0<(allOmittedPins p).card)) with h|h
  · exact off_five_connected_single_oriented preTable coreTable hc even conn degree hp ah bh len off H whole single h
  have rev : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have rlen : p.reverse.length=10 := by simpa using len
  have roff : ((univ : Finset V)\p.reverse.support.toFinset).card=5 := by simpa [support_reverse] using off
  let R : OmittedComponent p.reverse :=
    ⟨H.vertices,H.nonempty,(by intro z h; simpa using H.off z h),
      (by intro z hz w hw zw; simpa using H.closed z hz w hw zw),H.joined⟩
  have rwhole (z : V) (zo : z∉p.reverse.support) : z∈R.vertices := whole z (by simpa using zo)
  have rsingle (z : V) (zo : z∉p.reverse.support) : (Pins p.reverse z).card≤1 := by
    have old : z∉p.support := by simpa using zo
    have c := omittedDegree_eq hp.1 old
    have d := omittedDegree_eq rev.1 zo
    have agree : omittedNeighbors p.reverse z=omittedNeighbors p z := by simp [omittedNeighbors,support_reverse]
    rw [agree] at d
    have s := single z old
    omega
  exact off_five_connected_single_oriented preTable coreTable hc even conn degree rev bh ah rlen roff R rwhole rsingle h

#print axioms traceable_if_five_off_connected_single_with_table

end Graffiti189LongestPath.TwoCut.SmallOrderFour
