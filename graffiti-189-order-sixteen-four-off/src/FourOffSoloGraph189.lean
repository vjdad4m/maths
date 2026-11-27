import FourOffSoloExtras189
import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
open private omittedNeighbors omittedDegree_eq hamilton_of_labeled_chain from FourOffGraphCore189
open private mark_holes_of_pin_and_missing_endpoint from FourOffGraphSupport189

private theorem model16_off_four_solo_compatible
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=11)
    {i j c d : ℕ} (il : 1≤i) (ij : i+3≤j) (jl : j≤10)
    (φ : Fin 16→V)
    (on : ∀ k : Fin 16,k.val≤11 → φ k=p.getVert k.val)
    (out : ∀ k : Fin 16,12≤k.val → φ k∉p.support)
    (inj : Function.Injective φ)
    (least : ∀ k : Fin 16,12≤k.val → k.val<12+c → i∈Pins p (φ k))
    (later : ∀ k : Fin 16,12+c≤k.val → k.val<12+c+d → j∈Pins p (φ k))
    (clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w)
    (m : OffFour16Solo.Marks)
    (L : ∀ k : Fin 11,m k=1 ↔ G.Adj a (p.getVert (k.val+1)))
    (R : ∀ k : Fin 11,m k=2 ↔ G.Adj b (p.getVert k.val)) :
    (∀ u v,OffFour16Solo.edge i j c d m u v=true → G.Adj (φ u) (φ v)) ∧
    (∀ u,G.Adj (φ (0:Fin 16)) (φ u) → OffFour16Solo.edge i j c d m 0 u=true) ∧
    (∀ u,G.Adj (φ (11:Fin 16)) (φ u) → OffFour16Solo.edge i j c d m 11 u=true) := by
  have a0 : φ 0=a := by rw [on 0 (by decide)]; exact p.getVert_zero
  have b10 : φ 11=b := by rw [on 11 (by decide)]; simpa [len] using p.getVert_length
  have direction (u v : Fin 16) (h : OffFour16Solo.dir i j c d m u v=true) : G.Adj (φ u) (φ v) := by
    simp only [OffFour16Solo.dir,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with (((((ha|hb)|hc)|hd)|he)|hf)
    · rw [on u (by omega),on v ha.2,ha.1]
      exact p.adj_getVert_succ (by omega)
    · exact clique _ (out u hb.1) _ (out v (by omega)) (fun e => by
        have C := congrArg Fin.val (inj e)
        omega)
    · rw [on u (by omega),hc.1]
      exact (pin_data (least v hc.2.1 hc.2.2)).2.symm
    · rw [on u (by omega),hd.1]
      exact (pin_data (later v hd.2.1 hd.2.2)).2.symm
    · by_cases q : u.val=0 ∧ 1≤v.val ∧ v.val≤11
      · simp only [dif_pos q,decide_eq_true_eq] at he
        rw [on u (by omega),on v q.2.2,q.1,p.getVert_zero]
        have h := (L ⟨v.val-1,by omega⟩).mp he
        change G.Adj a (p.getVert (v.val-1+1)) at h
        rwa [show v.val-1+1=v.val by omega] at h
      · simp only [dif_neg q] at he
        contradiction
    · by_cases q : v.val=11 ∧ u.val<11
      · simp only [dif_pos q,decide_eq_true_eq] at hf
        rw [on u (by omega),on v (by omega),q.1,←len,p.getVert_length]
        exact ((R ⟨u.val,q.2⟩).mp hf).symm
      · simp only [dif_neg q] at hf
        contradiction
  refine ⟨?_,?_,?_⟩
  · intro u v h
    simp only [OffFour16Solo.edge,Bool.or_eq_true] at h
    exact h.elim (direction _ _) (fun e => G.symm (direction _ _ e))
  · intro u uA
    have onP : u.val≤11 := by
      by_contra no
      exact (no_endpoints hp (out u (by omega))).1 ((a0 ▸ uA).symm)
    have up : 1≤u.val := by
      by_contra no
      have u0 : u=0 := Fin.ext (show u.val=0 by omega)
      exact G.loopless _ (u0 ▸ uA)
    have q : (0:Fin 16).val=0 ∧ 1≤u.val ∧ u.val≤11 := ⟨rfl,up,onP⟩
    have ia : G.Adj a (p.getVert ((u.val-1)+1)) := by
      rw [show u.val-1+1=u.val by omega,←on u onP,←a0]
      exact uA
    have h : m ⟨u.val-1,by omega⟩=1 := (L _).mpr ia
    simp only [OffFour16Solo.edge,Bool.or_eq_true]
    left
    simp [OffFour16Solo.dir,q,h]
  · intro u uB
    have onP : u.val≤11 := by
      by_contra no
      exact (no_endpoints hp (out u (by omega))).2 ((b10 ▸ uB).symm)
    have up : u.val<11 := by
      by_contra no
      have u10 : u=11 := Fin.ext (show u.val=(11:Fin 16).val by change u.val=11; omega)
      exact G.loopless _ (u10 ▸ uB)
    have q : (11:Fin 16).val=11 ∧ u.val<11 := ⟨rfl,up⟩
    have ib : G.Adj b (p.getVert u.val) := by
      rw [←on u onP,←b10]
      exact uB
    have h : m ⟨u.val,up⟩=2 := (R _).mpr ib
    simp only [OffFour16Solo.edge,Bool.or_eq_true]
    right
    simp [OffFour16Solo.dir,q,h]
#print axioms model16_off_four_solo_compatible


private theorem model16_d2_upper_solo (hc : G.Connected)
    (φ : Fin 16 → V) (inj : Function.Injective φ)
    (E : Fin 16 → Fin 16 → Bool) (z : Fin 16)
    (forw : ∀ u v,E u v=true → G.Adj (φ u) (φ v))
    (rev : ∀ u,G.Adj (φ z) (φ u) → E z u=true)
    (cap : (DistanceTwo G (φ z)).card≤4) :
    (univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 16,E z u=true ∧ E u y=true).card≤4 := by
  classical
  let Q := univ.filter fun y => y≠z ∧ !E z y = true ∧
      ∃ u : Fin 16,E z u=true ∧ E u y=true
  have sub : Q.image φ ⊆ DistanceTwo G (φ z) := by
    intro y hy
    obtain ⟨v,vq,rfl⟩ := mem_image.mp hy
    obtain ⟨vne,no,w,zw,wv⟩ := (mem_filter.mp vq).2
    have ne : φ z≠φ v := fun e => vne (inj e).symm
    have no' : ¬G.Adj (φ z) (φ v) := fun e => by
      have r := rev v e
      simp [r] at no
    exact mem_distanceTwo.mpr (dist_two hc ne no' (forw z w zw) (forw w v wv))
  have c := card_le_card sub
  rw [card_image_of_injective _ inj] at c
  exact c.trans cap


/-- Apart from the two own flanks and the foreign port, the path
neighbors of a singleton port occupy at most one distance-two slot. -/
private theorem single_pin_path_neighbors_one_extra
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (xy : G.Adj x y)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y)
    (few : (Pins p x).card≤1) (gap : i+3≤j ∨ j+3≤i) :
    ((range (p.length+1)).filter (fun k => G.Adj (p.getVert i) (p.getVert k) ∧
      k≠i-1 ∧ k≠i+1 ∧ k≠j)).card≤1 := by
  classical
  let M := (range (p.length+1)).filter (fun k => G.Adj (p.getVert i) (p.getVert k) ∧
      k≠i-1 ∧ k≠i+1 ∧ k≠j)
  change M.card≤1
  by_contra n
  obtain ⟨k,km,l,lm,kl⟩ := one_lt_card.mp (Nat.lt_of_not_ge n)
  obtain ⟨kr,pk,k1,k2,k3⟩ := mem_filter.mp km
  obtain ⟨lr,pl,l1,l2,l3⟩ := mem_filter.mp lm
  have kkB : k≤p.length := by have t := mem_range.mp kr; omega
  have llB : l≤p.length := by have t := mem_range.mp lr; omega
  have ip := pin_pos hp xo hi
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ban {v : ℕ} (vle : v≤p.length) (ne : v≠i) : ¬G.Adj x (p.getVert v) := by
    intro e
    have vl : v<p.length := by
      by_contra q
      have ee : v=p.length := by omega
      rw [ee,p.getVert_length] at e
      exact (no_endpoints hp xo).2 e
    have h : v∈Pins p x := mem_filter.mpr ⟨mem_range.mpr vl,e⟩
    have m := one_lt_card.mpr ⟨i,hi,v,h,ne.symm⟩
    omega
  have δ1 : p.getVert (i-1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp xo (show p.getVert (i-1)∈FlankVertices p x from
      mem_image.mpr ⟨i-1,mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩))).1
  have δ2 : p.getVert (i+1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp xo (show p.getVert (i+1)∈FlankVertices p x from
      mem_image.mpr ⟨i+1,mem_union.mpr (.inr (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩))).1
  have δ3 : p.getVert j∈DistanceTwo G x := mem_distanceTwo.mpr
    (dist_two hc (fun e => xo (e ▸ p.getVert_mem_support j)) (ban jl.le (by omega)) xy (pin_data hj).2)
  have more {v : ℕ} (vl : v≤p.length) (e : G.Adj (p.getVert i) (p.getVert v)) :
      p.getVert v∈DistanceTwo G x :=
    mem_distanceTwo.mpr (dist_two hc (fun eq => xo (eq ▸ p.getVert_mem_support v))
      (ban vl (fun eq => G.loopless _ (eq ▸ e))) (pin_data hi).2 e)
  let T : Finset ℕ := {i-1,i+1,j,k,l}
  have C : T.card=5 := by
    have a : i-1∉({i+1,j,k,l}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have b : i+1∉({j,k,l}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have c : j∉({k,l}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have d : k∉({l}:Finset ℕ) := by simpa using kl
    rw [show T={i-1,i+1,j,k,l} from rfl,card_insert_of_not_mem a,card_insert_of_not_mem b,
      card_insert_of_not_mem c,card_insert_of_not_mem d,card_singleton]
  have ran {t : ℕ} (mt : t∈T) : t≤p.length := by
    have c : t=i-1 ∨ t=i+1 ∨ t=j ∨ t=k ∨ t=l := by simpa [T] using mt
    rcases c with rfl|rfl|rfl|rfl|rfl <;> omega
  have cardT : (T.image p.getVert).card=5 :=
    (card_image_iff.mpr (fun _ u _ v e => hp.1.getVert_injOn (ran u) (ran v) e)).trans C
  have sub : T.image p.getVert ⊆ DistanceTwo G x := by
    intro t h
    obtain ⟨z,zt,rfl⟩ := mem_image.mp h
    have c : z=i-1 ∨ z=i+1 ∨ z=j ∨ z=k ∨ z=l := by simpa [T] using zt
    rcases c with rfl|rfl|rfl|rfl|rfl
    · exact δ1
    · exact δ2
    · exact δ3
    · exact more kkB pk
    · exact more llB pl
  have d := card_le_card sub
  have cap := distanceTwo_le_of_even 4 x (even x)
  omega
#print axioms single_pin_path_neighbors_one_extra

open OffFour16Solo in
private theorem solo_select_exact_extra_on_path
    {a b : V} {p : G.Walk a b} (len : p.length=11)
    (φ : Fin 16→V) (value : ∀ v : Fin 16,v.val≤11 → φ v=p.getVert v.val)
    {i j x y u w : ℕ} (m : Marks)
    (uL : 1≤u) (uH : u≤10) (wL : 1≤w) (wH : w≤10)
    (forw : ∀ v z,edge i j x y m v z=true → G.Adj (φ v) (φ z))
    (end0 : ∀ v,G.Adj (φ 0) (φ v) → edge i j x y m 0 v=true)
    (end11 : ∀ v,G.Adj (φ 11) (φ v) → edge i j x y m 11 v=true)
    (slack : ((range (p.length+1)).filter (fun k => G.Adj (p.getVert u) (p.getVert k) ∧
      k≠u-1 ∧ k≠u+1 ∧ k≠w)).card≤1) :
    ∃ r∈optSites i j x y m u w,
      (r≠atPort u → G.Adj (φ (atPort u)) (φ r)) ∧
      ∀ v : Fin 16,v.val≤11 → G.Adj (φ (atPort u)) (φ v) →
        edge i j x y m (atPort u) v=true ∨ v=atPort w ∨ (r≠atPort u ∧ v=r) := by
  classical
  let E := edge i j x y m
  let S := (range (p.length+1)).filter (fun k => G.Adj (p.getVert u) (p.getVert k) ∧
      k≠u-1 ∧ k≠u+1 ∧ k≠w)
  have su : S.card≤1 := slack
  have uv : (atPort u).val=u := Nat.mod_eq_of_lt (by omega)
  have wv : (atPort w).val=w := Nat.mod_eq_of_lt (by omega)
  have uv' : φ (atPort u)=p.getVert u := by rw [value _ (by rw [uv]; omega),uv]
  have Eflip (v t : Fin 16) : E v t=E t v := by simp only [E,edge,Bool.or_comm]
  have contain {k h : ℕ} (kk : k∈S) (hh : h∈S) : k=h := by
    by_contra ne
    have b := one_lt_card.mpr ⟨k,kk,h,hh,ne⟩
    omega
  have toS (v : Fin 16) (vl : v.val≤11) (h : G.Adj (φ (atPort u)) (φ v))
      (one : v.val≠u-1) (two : v.val≠u+1) (other : v.val≠w) : v.val∈S :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [uv',value _ vl] at h,one,two,other⟩
  have flankBits (v : Fin 16) (e : v.val=u-1 ∨ v.val=u+1) : E (atPort u) v=true := by
    rcases e with e|e
    · have a : (atPort u).val=v.val+1 := by omega
      have b : v.val+1≤11 := by omega
      simp [E,edge,dir,a,b]
    · have a : v.val=(atPort u).val+1 := by omega
      have b : (atPort u).val+1≤11 := by omega
      simp [E,edge,dir,a,b]
  have baseline (v : Fin 16) (vl : v.val≤11) (h : G.Adj (φ (atPort u)) (φ v)) :
      E (atPort u) v=true ∨ v=atPort w ∨ v.val∈S := by
    by_cases eqW : v=atPort w
    · exact .inr (.inl eqW)
    by_cases f : v.val=u-1 ∨ v.val=u+1
    · exact .inl (flankBits v f)
    exact .inr (.inr (toS v vl h (fun e => f (.inl e)) (fun e => f (.inr e))
      (fun e => eqW (Fin.ext (e.trans wv.symm)))))
  by_cases known : knownExtra i j x y m u=true
  · refine ⟨atPort u,by simp [optSites,known],fun n => (n rfl).elim,?_⟩
    have two : (u≠1 ∧ E (atPort u) 0=true) ∨ (u≠10 ∧ E (atPort u) 11=true) := by
      simpa only [knownExtra,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,E] using known
    obtain ⟨k,km,ke,kv⟩ : ∃ k : Fin 16,k.val∈S ∧ E (atPort u) k=true ∧ (k=0 ∨ k=11) := by
      rcases two with ⟨ne,e⟩|⟨ne,e⟩
      · exact ⟨0,toS 0 (by decide) (forw _ _ e) (by change 0≠u-1; omega)
          (by change 0≠u+1; omega) (by change 0≠w; omega),e,.inl rfl⟩
      · exact ⟨11,toS 11 (by decide) (forw _ _ e) (by change 11≠u-1; omega)
          (by change 11≠u+1; omega) (by change 11≠w; omega),e,.inr rfl⟩
    intro v vl h
    rcases baseline v vl h with e|e|e
    · exact .inl e
    · exact .inr (.inl e)
    · have eq : v=k := Fin.ext (contain e km)
      exact .inl (eq.symm ▸ ke)
  have knownf : knownExtra i j x y m u=false := Bool.eq_false_iff.mpr known
  by_cases h : S.Nonempty
  · obtain ⟨k,km⟩ := h
    obtain ⟨kr,ek,k1,k2,k3⟩ := mem_filter.mp km
    have kl : k≤11 := by have o := mem_range.mp kr; omega
    have kub : k≠u := fun eq => G.loopless _ (eq ▸ ek)
    let r : Fin 16 := ⟨k,by omega⟩
    have ar : G.Adj (φ (atPort u)) (φ r) := by rw [uv',value r (by exact kl)]; exact ek
    have k0 : k≠0 := by
      intro e
      have eq : r=0 := Fin.ext e
      have yes : E (atPort u) 0=true := by
        rw [Eflip]; exact end0 _ (by simpa only [eq] using ar.symm)
      have u1 : u≠1 := by omega
      have H : knownExtra i j x y m u=true := by simp [knownExtra,u1,show edge i j x y m (atPort u) 0=true from yes]
      exact known H
    have k11 : k≠11 := by
      intro e
      have eq : r=11 := Fin.ext e
      have yes : E (atPort u) 11=true := by
        rw [Eflip]; exact end11 _ (by simpa only [eq] using ar.symm)
      have u10 : u≠10 := by omega
      have H : knownExtra i j x y m u=true := by simp [knownExtra,u10,show edge i j x y m (atPort u) 11=true from yes]
      exact known H
    have ro : r∈optSites i j x y m u w := by
      simp only [optSites,knownf,Bool.false_eq_true,if_false,List.mem_cons]
      apply Or.inr
      exact List.mem_filter.mpr ⟨List.mem_finRange _,by
        apply decide_eq_true
        change 1≤k ∧ k≤10 ∧ k≠u ∧ k≠u-1 ∧ k≠u+1 ∧ k≠w
        exact ⟨by omega,by omega,kub,k1,k2,k3⟩⟩
    have rn : r≠atPort u := fun e => kub ((congrArg Fin.val e).trans uv)
    refine ⟨r,ro,fun _ => ar,?_⟩
    intro v vl h
    rcases baseline v vl h with h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨rn,Fin.ext (contain h km)⟩)
  · refine ⟨atPort u,by simp [optSites,knownf],fun n => (n rfl).elim,?_⟩
    intro v vl hv
    rcases baseline v vl hv with e|e|e
    · exact .inl e
    · exact .inr (.inl e)
    · exact (h ⟨_,e⟩).elim

#print axioms solo_select_exact_extra_on_path

open OffFour16Solo in
private theorem solo_model_cannot_be_exception
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=11)
    {i j n d : ℕ} (iL : 1≤i) (gap : i+3≤j) (jH : j≤10)
    (hi : i∈Pins p x) (hj : j∈Pins p y)
    (xo : x∉p.support) (yo : y∉p.support) (xy : G.Adj x y)
    (xc : (Pins p x).card≤1) (yc : (Pins p y).card≤1)
    (φ : Fin 16→V) (inj : Function.Injective φ)
    (value : ∀ v : Fin 16,v.val≤11 → φ v=p.getVert v.val)
    (pinI : ∀ v : Fin 16,12≤v.val → (i∈Pins p (φ v) ↔ v.val<12+n))
    (pinJ : ∀ v : Fin 16,12≤v.val → (j∈Pins p (φ v) ↔ 12+n≤v.val ∧ v.val<12+n+d))
    (m : Marks)
    (forw : ∀ v w,edge i j n d m v w=true → G.Adj (φ v) (φ w))
    (end0 : ∀ v,G.Adj (φ 0) (φ v) → edge i j n d m 0 v=true)
    (end11 : ∀ v,G.Adj (φ 11) (φ v) → edge i j n d m 11 v=true)
    (bad : exceptional i j n d m=true) : False := by
  classical
  have li := single_pin_path_neighbors_one_extra hc even hp xo xy hi hj xc (.inl gap)
  have lj := single_pin_path_neighbors_one_extra hc even hp yo xy.symm hj hi yc (.inr gap)
  obtain ⟨r,ro,ra,ri⟩ := solo_select_exact_extra_on_path len φ value m
    iL (by omega) (by omega : 1≤j) jH forw end0 end11 li
  obtain ⟨s,so,sa,sj⟩ := solo_select_exact_extra_on_path len φ value m
    (by omega : 1≤j) jH iL (by omega) forw end0 end11 lj
  let I := atPort i
  let J := atPort j
  have iv : I.val=i := Nat.mod_eq_of_lt (by omega)
  have jv : J.val=j := Nat.mod_eq_of_lt (by omega)
  have iv' : φ I=p.getVert i := by rw [value _ (by rw [iv]; omega),iv]
  have jv' : φ J=p.getVert j := by rw [value _ (by rw [jv]; omega),jv]
  let e := decide (G.Adj (φ I) (φ J))
  let E := edgeAug i j n d m e r s
  have F (v w : Fin 16) (h : E v w=true) : G.Adj (φ v) (φ w) := by
    simp only [E,edgeAug,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,pair] at h
    rcases h with (((a|⟨a,b⟩)|⟨c,f⟩)|⟨c,f⟩)
    · exact forw _ _ a
    · have A : G.Adj (φ I) (φ J) := of_decide_eq_true a
      rcases b with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact A
      · exact A.symm
    · rcases f with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ra c
      · exact (ra c).symm
    · rcases f with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact sa c
      · exact (sa c).symm
  have REi (v : Fin 16) (h : G.Adj (φ I) (φ v)) : E I v=true := by
    by_cases vp : v.val≤11
    · rcases ri v vp h with base|cross|⟨hr,hv⟩
      · simp [E,edgeAug,I,base]
      · have hv : v=J := cross
        subst v
        simp [E,edgeAug,pair,e,I,J,h]
      · subst v
        simp [E,edgeAug,pair,I,hr]
    have vO : 12≤v.val := by omega
    have pin : i∈Pins p (φ v) := mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [iv'] at h; exact h.symm⟩
    have k := (pinI v vO).mp pin
    simp [E,edgeAug,edge,dir,iv,vO,k]
  have REj (v : Fin 16) (h : G.Adj (φ J) (φ v)) : E J v=true := by
    by_cases vp : v.val≤11
    · rcases sj v vp h with base|cross|⟨hs,hv⟩
      · simp [E,edgeAug,J,base]
      · have hv : v=I := cross
        subst v
        simp [E,edgeAug,pair,e,I,J,h.symm]
      · subst v
        simp [E,edgeAug,pair,J,hs]
    have vO : 12≤v.val := by omega
    have pin : j∈Pins p (φ v) := mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [jv'] at h; exact h.symm⟩
    have k := (pinJ v vO).mp pin
    simp [E,edgeAug,edge,dir,jv,k.1,k.2]
  have cap := fun v => distanceTwo_le_of_even 4 v (even v)
  have dI : (d2Aug i j n d m e r s I).card≤4 := model16_d2_upper_solo hc φ inj E I F REi (cap _)
  have dJ : (d2Aug i j n d m e r s J).card≤4 := model16_d2_upper_solo hc φ inj E J F REj (cap _)
  exact actual_exc_reject bad ro so dI dJ
#print axioms solo_model_cannot_be_exception

private theorem model16_off_four_solo_marks
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=11)
    (xo : x∉p.support) (yo : y∉p.support) {i j : ℕ}
    (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i+3≤j)
    (lah : ¬G.Adj a (p.getVert i) ∨ ¬G.Adj a (p.getVert j))
    (lbh : ¬G.Adj b (p.getVert i) ∨ ¬G.Adj b (p.getVert j))
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) :
    ∃ (m : OffFour16Solo.Marks) (s t : ℕ),
      OffFour16Solo.fit i j s t=true ∧ m 0=1 ∧ m 10=2 ∧
      (∀ k : Fin 11, OffFour16Solo.Hole k.val s t → m k=0) ∧
      ((OffFour16Solo.sites s t).map m).count 0≤1 ∧
      4≤OffFour16Solo.markCount m 1 ∧ 4≤OffFour16Solo.markCount m 2 ∧
      OffFour16Solo.PinsAllowed i j m=true ∧
      (∀ k : Fin 11, m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 11, m k=2 ↔ G.Adj b (p.getVert k.val)) := by
  classical
  have px := (pin_data hi).2
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support i) px kr h.1 h.2
  let m : OffFour16Solo.Marks := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 11) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 11) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have zero (k : Fin 11) : m k=0 ↔ k.val∉LeftMarks p∪RightMarks p := by
    have kr : k.val<p.length := by have ee := k.isLt; omega
    have km : k.val∈range p.length := mem_range.mpr kr
    by_cases al : G.Adj a (p.getVert (k.val+1)) <;>
      by_cases br : G.Adj b (p.getVert k.val) <;> simp [m,al,br,LeftMarks,RightMarks,km]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m10 : m 10=2 := (r 10).mpr (by
    have rr := (p.adj_getVert_succ (i:=10) (by omega)).symm
    rw [show 10+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ip := pin_pos hp xo hi
  have jp := pin_pos hp yo hj
  obtain ⟨s,sr,sh⟩ : ∃ s : ℕ,(s=i-1 ∨ s=j-1) ∧ s∉LeftMarks p∪RightMarks p := lah.elim
    (fun h => ⟨i-1,.inl rfl,(mark_holes_of_pin_and_missing_endpoint hp xo hi).1 h⟩)
    (fun h => ⟨j-1,.inr rfl,(mark_holes_of_pin_and_missing_endpoint hp yo hj).1 h⟩)
  obtain ⟨t,tr,th⟩ : ∃ t : ℕ,(t=i ∨ t=j) ∧ t∉LeftMarks p∪RightMarks p := lbh.elim
    (fun h => ⟨i,.inl rfl,(mark_holes_of_pin_and_missing_endpoint hp xo hi).2 h⟩)
    (fun h => ⟨j,.inr rfl,(mark_holes_of_pin_and_missing_endpoint hp yo hj).2 h⟩)
  have st : s≠t := by omega
  have sl : s<11 := by omega
  have tl : t<11 := by omega
  have s0 : s≠0 := fun eq => by
    have z := (zero ⟨s,sl⟩).mpr sh
    have e : (⟨s,sl⟩:Fin 11)=0 := Fin.ext eq
    rw [e,m0] at z
    exact (by decide : (1:Fin 3)≠0) z
  have t9 : t≠10 := fun eq => by
    have z := (zero ⟨t,tl⟩).mpr th
    have e : (⟨t,tl⟩:Fin 11)=10 := Fin.ext eq
    rw [e,m10] at z
    exact (by decide : (2:Fin 3)≠0) z
  refine ⟨m,s,t,(show OffFour16Solo.fit i j s t=true by
    exact decide_eq_true ⟨by omega,by omega,by omega,by omega,sr,tr⟩),m0,m10,?_,?_,?_,?_,?_,l,r⟩
  · intro k h
    rcases h with e|e
    · exact (zero k).mpr (e.symm ▸ sh)
    · exact (zero k).mpr (e.symm ▸ th)

  · let L := (OffFour16Solo.sites s t).filter (fun k => m k == 0)
    have ns : (OffFour16Solo.sites s t).Nodup := (List.nodup_finRange 11).filter _
    have nd : L.Nodup := ns.filter _
    have eqC : ((OffFour16Solo.sites s t).map m).count 0=L.length := by
      rw [List.count,List.countP_map,List.countP_eq_length_filter]
      rfl
    let Q := L.toFinset.image (Fin.val : Fin 11→ℕ)
    have cQ : Q.card=L.length := by
      change (L.toFinset.image (Fin.val : Fin 11→ℕ)).card=L.length
      rw [card_image_of_injective _ (fun _ _ h => Fin.ext h),List.toFinset_card_of_nodup nd]
    have Hq {k : ℕ} (kQ : k∈Q) :
        k<p.length ∧ k≠s ∧ k≠t ∧ k∉LeftMarks p∪RightMarks p := by
      obtain ⟨v,vL,rfl⟩ := mem_image.mp kQ
      obtain ⟨vs,vm⟩ := List.mem_filter.mp (List.mem_toFinset.mp vL)
      have z : m v=0 := beq_iff_eq.mp vm
      have no : ¬OffFour16Solo.Hole v.val s t := (of_decide_eq_true (List.mem_filter.mp vs).2).2.2
      have r := v.isLt
      exact ⟨by omega,fun eq => no (.inl eq),fun eq => no (.inr eq),(zero v).mp z⟩
    let M := insert s (insert t Q)
    have cM : M.card=Q.card+2 := by
      have tn : t∉Q := fun h => (Hq h).2.2.1 rfl
      have sn : s∉insert t Q := fun h => (mem_insert.mp h).elim st (fun e => (Hq e).2.1 rfl)
      change (insert s (insert t Q)).card=Q.card+2
      rw [card_insert_of_not_mem sn,card_insert_of_not_mem tn]
    have br : M⊆range p.length := by
      intro k km
      have h := mem_insert.mp km
      rcases h with rfl|h
      · exact mem_range.mpr (by omega)
      rcases mem_insert.mp h with rfl|h
      · exact mem_range.mpr (by omega)
      · exact mem_range.mpr (Hq h).1
    have dm : Disjoint (LeftMarks p∪RightMarks p) M := by
      apply disjoint_left.mpr
      intro k ka km
      rcases mem_insert.mp km with rfl|h
      · exact sh ka
      rcases mem_insert.mp h with rfl|h
      · exact th ka
      · exact (Hq h).2.2.2 ka
    have bd := mark_length hp xo (p.getVert_mem_support i) px M br dm
    omega
  · unfold OffFour16Solo.markCount
    let N := univ.filter (fun k : Fin 11 => m k=1)
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
    change 4≤N.card
    rw [←ce,eq,card_leftMarks hp]
    exact ah
  · unfold OffFour16Solo.markCount
    let N := univ.filter (fun k : Fin 11 => m k=2)
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
    change 4≤N.card
    rw [←ce,eq,card_rightMarks hp]
    exact bh
  · apply List.all_eq_true.mpr
    intro k _
    apply decide_eq_true
    constructor
    · intro hm lk
      have la := (l k).mp lk
      exact hm.elim
        (fun h => start_not_adj_pin_successor hp xo hi (by rwa [h] at la))
        (fun h => start_not_adj_pin_successor hp yo hj (by rwa [h] at la))
    · intro hm rk
      have ra := (r k).mp rk
      exact hm.elim
        (fun h => end_not_adj_pin_predecessor hp xo hi (by rwa [show i-1=k.val by omega]))
        (fun h => end_not_adj_pin_predecessor hp yo hj (by rwa [show j-1=k.val by omega]))
#print axioms model16_off_four_solo_marks

private theorem model16_off_four_solo_labels
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (xo : x∉p.support) (yo : y∉p.support) {i j : ℕ}
    (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i+3≤j)
    (few : ∀ z∉p.support,(Pins p z).card≤1)
    (ports : ∀ z∉p.support,Pins p z⊆({i,j}:Finset ℕ)) :
    ∃ (c d : ℕ) (φ : Fin 16→V),
      (c,d)∈([(1,2),(2,1),(1,3),(2,2),(3,1)]:List (ℕ×ℕ)) ∧
      Function.Injective φ ∧ (∀ k : Fin 16,k.val≤11 → φ k=p.getVert k.val) ∧
      (∀ k : Fin 16,12≤k.val → φ k∉p.support) ∧
      (∀ k : Fin 16,12≤k.val → (i∈Pins p (φ k) ↔ k.val<12+c)) ∧
      (∀ k : Fin 16,12≤k.val → (j∈Pins p (φ k) ↔ 12+c≤k.val ∧ k.val<12+c+d)) := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  let A := O.filter (fun z => i∈Pins p z)
  let B := O.filter (fun z => j∈Pins p z)
  let C := O\(A∪B)
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have oc : O.card=4 := off
  have disAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro z a b
    have f := few z (out.mp (mem_filter.mp a).1)
    have q := one_lt_card.mpr ⟨i,(mem_filter.mp a).2,j,(mem_filter.mp b).2,by omega⟩
    omega
  have cd : A.card+B.card+C.card=4 := by
    have h := card_sdiff_add_card_eq_card
      (show A∪B⊆O from union_subset (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint disAB] at h
    change C.card+(A.card+B.card)=O.card at h
    omega
  have posA : 0<A.card := card_pos.mpr ⟨x,mem_filter.mpr ⟨out.mpr xo,hi⟩⟩
  have posB : 0<B.card := card_pos.mpr ⟨y,mem_filter.mpr ⟨out.mpr yo,hj⟩⟩
  have Csmall : C.card≤1 := by
    by_contra n
    obtain ⟨u,um,v,vm,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge n)
    have clow {z : V} (zc : z∈C) : ¬4≤G.degree z := by
      have zO := (mem_sdiff.mp zc).1
      have zo := out.mp zO
      intro zh
      have d := degree_off_bound hp zo
      rw [off] at d
      obtain ⟨k,km⟩ := card_pos.mp (show 0<(Pins p z).card by omega)
      have ks := ports z zo km
      rcases mem_insert.mp ks with rfl|ks
      · exact (mem_sdiff.mp zc).2 (mem_union.mpr (.inl (mem_filter.mpr ⟨zO,km⟩)))
      · obtain rfl := mem_singleton.mp ks
        exact (mem_sdiff.mp zc).2 (mem_union.mpr (.inr (mem_filter.mpr ⟨zO,km⟩)))
    exact (degree u v ne).elim (clow um) (clow vm)
  let eA : Fin A.card ≃ A := (Fintype.equivFinOfCardEq (by simp)).symm
  let eB : Fin B.card ≃ B := (Fintype.equivFinOfCardEq (by simp)).symm
  let eC : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (by simp)).symm
  let φ : Fin 16→V := fun v =>
    if h : v.val≤11 then p.getVert v.val else
    if k : v.val<12+A.card then (eA ⟨v.val-12,by omega⟩).val else
    if l : v.val<12+A.card+B.card then (eB ⟨v.val-(12+A.card),by omega⟩).val else
      (eC ⟨v.val-(12+A.card+B.card),by have W := v.isLt; omega⟩).val
  have on {v : Fin 16} (vh : v.val≤11) : φ v=p.getVert v.val := by simp [φ,vh]
  have a_label {v : Fin 16} (vl : 12≤v.val) (vu : v.val<12+A.card) :
      φ v=(eA ⟨v.val-12,by omega⟩).val := by
    simp [φ,show ¬v.val≤11 by omega,vu]
  have b_label {v : Fin 16} (vl : 12+A.card≤v.val) (vu : v.val<12+A.card+B.card) :
      φ v=(eB ⟨v.val-(12+A.card),by omega⟩).val := by
    simp [φ,show ¬v.val≤11 by omega,show ¬v.val<12+A.card by omega,vu]
  have c_label {v : Fin 16} (vl : 12+A.card+B.card≤v.val) :
      φ v=(eC ⟨v.val-(12+A.card+B.card),by have W := v.isLt; omega⟩).val := by
    simp [φ,show ¬v.val≤11 by omega,show ¬v.val<12+A.card by omega,show ¬v.val<12+A.card+B.card by omega]
  have a_mem {v : Fin 16} (vl : 12≤v.val) (vu : v.val<12+A.card) : φ v∈A := by
    rw [a_label vl vu]
    exact Subtype.property _
  have b_mem {v : Fin 16} (vl : 12+A.card≤v.val) (vu : v.val<12+A.card+B.card) : φ v∈B := by
    rw [b_label vl vu]
    exact Subtype.property _
  have c_mem {v : Fin 16} (vl : 12+A.card+B.card≤v.val) : φ v∈C := by
    rw [c_label vl]
    exact Subtype.property _
  have offLabel {v : Fin 16} (vl : 12≤v.val) : φ v∉p.support := by
    apply out.mp
    by_cases va : v.val<12+A.card
    · exact (mem_filter.mp (a_mem vl va)).1
    by_cases vb : v.val<12+A.card+B.card
    · exact (mem_filter.mp (b_mem (by omega) vb)).1
    exact (mem_sdiff.mp (c_mem (by omega))).1
  have inj : Function.Injective φ := by
    intro u v uv
    apply Fin.ext
    by_cases up : u.val≤11 <;> by_cases vp : v.val≤11
    · exact hp.1.getVert_injOn (show u.val≤p.length by omega) (show v.val≤p.length by omega)
        ((on up).symm.trans (uv.trans (on vp)))
    · exact False.elim (offLabel (show 12≤v.val by omega)
        (uv ▸ ((on up).symm ▸ p.getVert_mem_support u.val)))
    · exact False.elim (offLabel (show 12≤u.val by omega)
        (uv.symm ▸ ((on vp).symm ▸ p.getVert_mem_support v.val)))
    have ul : 12≤u.val := by omega
    have vl : 12≤v.val := by omega
    by_cases ua : u.val<12+A.card <;> by_cases va : v.val<12+A.card
    · rw [a_label ul ua,a_label vl va] at uv
      have eq := congrArg Fin.val (eA.injective (Subtype.ext uv))
      change u.val-12=v.val-12 at eq
      omega
    · have uA := a_mem ul ua
      by_cases vb : v.val<12+A.card+B.card
      · exact False.elim ((disjoint_left.mp disAB) (uv ▸ uA) (b_mem (by omega) vb))
      · exact False.elim ((mem_sdiff.mp (c_mem (show 12+A.card+B.card≤v.val by omega))).2
          (mem_union.mpr (.inl (uv ▸ uA))))
    · have vA := a_mem vl va
      by_cases ub : u.val<12+A.card+B.card
      · exact False.elim ((disjoint_left.mp disAB) (uv.symm ▸ vA) (b_mem (by omega) ub))
      · exact False.elim ((mem_sdiff.mp (c_mem (show 12+A.card+B.card≤u.val by omega))).2
          (mem_union.mpr (.inl (uv.symm ▸ vA))))
    by_cases ub : u.val<12+A.card+B.card <;> by_cases vb : v.val<12+A.card+B.card
    · rw [b_label (show 12+A.card≤u.val by omega) ub,b_label (show 12+A.card≤v.val by omega) vb] at uv
      have eq := congrArg Fin.val (eB.injective (Subtype.ext uv))
      change u.val-(12+A.card)=v.val-(12+A.card) at eq
      omega
    · have uB := b_mem (show 12+A.card≤u.val by omega) ub
      exact False.elim ((mem_sdiff.mp (c_mem (show 12+A.card+B.card≤v.val by omega))).2
        (mem_union.mpr (.inr (uv ▸ uB))))
    · have vB := b_mem (show 12+A.card≤v.val by omega) vb
      exact False.elim ((mem_sdiff.mp (c_mem (show 12+A.card+B.card≤u.val by omega))).2
        (mem_union.mpr (.inr (uv.symm ▸ vB))))
    · rw [c_label (show 12+A.card+B.card≤u.val by omega),
        c_label (show 12+A.card+B.card≤v.val by omega)] at uv
      have eq := congrArg Fin.val (eC.injective (Subtype.ext uv))
      change u.val-(12+A.card+B.card)=v.val-(12+A.card+B.card) at eq
      omega

  have xcmp (k : Fin 16) (kl : 12≤k.val) : i∈Pins p (φ k) ↔ k.val<12+A.card := by
    constructor
    · intro hk
      by_contra not
      have inA : φ k∈A := mem_filter.mpr ⟨out.mpr (offLabel kl),hk⟩
      by_cases b : k.val<12+A.card+B.card
      · exact (disjoint_left.mp disAB) inA (b_mem (by omega) b)
      · exact (mem_sdiff.mp (c_mem (by omega))).2 (mem_union.mpr (.inl inA))
    · intro kh
      exact (mem_filter.mp (a_mem kl kh)).2
  have ycmp (k : Fin 16) (kl : 12≤k.val) :
      j∈Pins p (φ k) ↔ 12+A.card≤k.val ∧ k.val<12+A.card+B.card := by
    constructor
    · intro hk
      have inB : φ k∈B := mem_filter.mpr ⟨out.mpr (offLabel kl),hk⟩
      have ka : 12+A.card≤k.val := by
        by_contra not
        exact (disjoint_left.mp disAB) (a_mem kl (by omega)) inB
      have kb : k.val<12+A.card+B.card := by
        by_contra not
        exact (mem_sdiff.mp (c_mem (by omega))).2 (mem_union.mpr (.inr inB))
      exact ⟨ka,kb⟩
    · intro kh
      exact (mem_filter.mp (b_mem kh.1 kh.2)).2
  refine ⟨A.card,B.card,φ,?_,inj,(fun _ h => on h),(fun _ h => offLabel h),xcmp,ycmp⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  omega
#print axioms model16_off_four_solo_labels
open OffFour16Solo in
private theorem length_eleven_four_off_single_pin_oriented
    (table : ∀ i j : ℕ,1≤i → i+3≤j → i≤11-j → j≤10 → row i j=true)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (xo : x∉p.support) (yo : y∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y)
    (gap : i+3≤j) (orient : i≤11-j)
    (few : ∀ z∉p.support,(Pins p z).card≤1)
    (ports : ∀ z∉p.support,Pins p z⊆({i,j}:Finset ℕ))
    (clique : ∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w)
    (la : ¬G.Adj a (p.getVert i) ∨ ¬G.Adj a (p.getVert j))
    (rb : ¬G.Adj b (p.getVert i) ∨ ¬G.Adj b (p.getVert j)) :
    ∃ a b : V, ∃ q : G.Walk a b,q.IsPath ∧ ∀ v,v∈q.support := by
  classical
  have ir := pin_pos hp xo hi
  have jlt := (pin_data hj).1
  have jr : j≤10 := by omega
  have xy : x≠y := by
    intro eq
    subst y
    have g := one_lt_card.mpr ⟨i,hi,j,hj,by omega⟩
    have sm := few x xo
    omega
  obtain ⟨m,s,t,F,m0,m10,hole,spars,cL,cR,ok,L,R⟩ :=
    model16_off_four_solo_marks hp len xo yo hi hj gap la rb ah bh
  obtain ⟨c,d,φ,cd,inj,value,out,pinI,pinJ⟩ :=
    model16_off_four_solo_labels hp len off degree xo yo hi hj gap few ports
  obtain ⟨forw,end0,end11⟩ := model16_off_four_solo_compatible hp len ir gap jr φ value out inj
    (fun k ko kr => (pinI k ko).mpr kr)
    (fun k kl kr => (pinJ k (by omega)).mpr ⟨kl,kr⟩) clique m L R
  have cap := fun z => distanceTwo_le_of_even 4 z (even z)
  have D0 : (d2Set i j c d m 0).card≤4 := model16_d2_upper_solo hc φ inj _ 0 forw end0 (cap _)
  have D11 : (d2Set i j c d m 11).card≤4 := model16_d2_upper_solo hc φ inj _ 11 forw end11 (cap _)
  rcases check_row (table i j ir gap orient jr) cd F m0 m10 hole spars cL cR ok D0 D11 with spans|exc
  · obtain ⟨l,nd,all,chain⟩ := spans
    have cardV : Fintype.card V=16 := by
      have q := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
      rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support,len,card_univ,off] at q
      exact q.symm
    have sur : Function.Surjective φ := by
      by_contra h
      have c := Fintype.card_lt_of_injective_not_surjective φ inj h
      rw [Fintype.card_fin,cardV] at c
      exact (Nat.lt_irrefl 16) c
    letI : Nonempty V := ⟨a⟩
    exact hamilton_of_labeled_chain φ inj sur l nd all (chain.imp (fun v w h => forw v w h))
  exact False.elim (solo_model_cannot_be_exception hc even hp len ir gap jr hi hj xo yo
    (clique _ xo _ yo xy) (few _ xo) (few _ yo) φ inj value pinI pinJ m forw end0 end11 exc)


#print axioms length_eleven_four_off_single_pin_oriented
theorem traceable_if_four_off_order_sixteen_all_single_pins_with_table
    (table : ∀ i j : ℕ,1≤i → i+3≤j → i≤11-j → j≤10 → OffFour16Solo.row i j=true)
    (shape : ∀ (_hc : G.Connected) (_even : ∀ v,(EvenFrom G v).card≤5)
    (_conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (_degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (_hp : EdgeOptimal p)
    (_ah : 4≤G.degree a) (_bh : 4≤G.degree b) (_len : p.length=11)
    (_off : ((univ : Finset V)\p.support.toFinset).card=4)
    (_few : ∀ x∉p.support,(Pins p x).card≤1) ,
    ∃ (x y : V) (i j : ℕ), x∉p.support ∧ y∉p.support ∧ i∈Pins p x ∧ j∈Pins p y ∧ i+3≤j ∧
      (∀ z∉p.support, Pins p z⊆({i,j}:Finset ℕ)) ∧
      (∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) ∧
      (¬G.Adj a (p.getVert i) ∨ ¬G.Adj a (p.getVert j)) ∧
      (¬G.Adj b (p.getVert i) ∨ ¬G.Adj b (p.getVert j)))
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : p.length=11) (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (few : ∀ z∉p.support,(Pins p z).card≤1) :
    ∃ a b : V, ∃ q : G.Walk a b,q.IsPath ∧ ∀ v,v∈q.support := by
  obtain ⟨x,y,i,j,xo,yo,hi,hj,gap,ports,clique,la,rb⟩ :=
    shape hc even conn degree hp ah bh len off few
  by_cases ord : i≤11-j
  · exact length_eleven_four_off_single_pin_oriented table hc even degree hp.1 ah bh len off
      xo yo hi hj gap ord few ports clique la rb
  have rev : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
  have rlen : p.reverse.length=11 := by simpa using len
  have ro : ((univ : Finset V)\p.reverse.support.toFinset).card=4 := by simpa [support_reverse] using off
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ryo : y∉p.reverse.support := by simpa using yo
  have rxo : x∉p.reverse.support := by simpa using xo
  have rhi : 11-j∈Pins p.reverse y := by simpa [len] using reverse_pin hp.1 yo hj
  have rhj : 11-i∈Pins p.reverse x := by simpa [len] using reverse_pin hp.1 xo hi
  have eqi : p.reverse.getVert (11-i)=p.getVert i := by rw [getVert_reverse,show p.length-(11-i)=i by omega]
  have eqj : p.reverse.getVert (11-j)=p.getVert j := by rw [getVert_reverse,show p.length-(11-j)=j by omega]
  have fewer (z : V) (zo : z∉p.reverse.support) : (Pins p.reverse z).card≤1 := by
    have zp : z∉p.support := by simpa using zo
    have d := omittedDegree_eq hp.1 zp
    have dr := omittedDegree_eq rev.1 zo
    have agree : omittedNeighbors p.reverse z=omittedNeighbors p z := by simp [omittedNeighbors,support_reverse]
    rw [agree] at dr
    have f := few z zp
    omega
  have pins (z : V) (zo : z∉p.reverse.support) : Pins p.reverse z⊆({11-j,11-i}:Finset ℕ) := by
    intro k hk
    have zp : z∉p.support := by simpa using zo
    have on : p.reverse.getVert k∈p.support := by
      simpa [support_reverse] using p.reverse.getVert_mem_support k
    obtain ⟨h,hm,eq⟩ := pin_of_neighbor_mem hp.1 zp on (pin_data hk).2
    rw [getVert_reverse] at eq
    have q := hp.1.1.getVert_injOn (pin_data hm).1.le (Nat.sub_le _ _) eq
    have quo : h=i ∨ h=j := by simpa using ports z zp hm
    have kk := (pin_data hk).1
    have r : k=11-j ∨ k=11-i := by omega
    simpa using r
  have C : ∀ z∉p.reverse.support,∀ w∉p.reverse.support,z≠w → G.Adj z w := by
    simpa only [support_reverse,List.mem_reverse] using clique
  have rL : ¬G.Adj b (p.reverse.getVert (11-j)) ∨ ¬G.Adj b (p.reverse.getVert (11-i)) := by
    rw [eqi,eqj]
    exact rb.symm
  have rR : ¬G.Adj a (p.reverse.getVert (11-j)) ∨ ¬G.Adj a (p.reverse.getVert (11-i)) := by
    rw [eqi,eqj]
    exact la.symm
  exact length_eleven_four_off_single_pin_oriented table hc even degree rev.1 bh ah rlen ro
    ryo rxo rhi rhj (by omega) (by omega) fewer pins C rL rR

#print axioms traceable_if_four_off_order_sixteen_all_single_pins_with_table
end Graffiti189LongestPath.TwoCut.SmallOrderFour
