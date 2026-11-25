/-
Graffiti.pc #138 counterexample, Written on the Wall II:
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/
Use a path on 15 vertices and attach two new leaves to each endpoint.
The longest induced path uses 17 vertices. The two degree maximizers in
the square graph are the two handle vertices next to its ends; their
square-graph distance is 6. The 11-vertex maximum independent set is
unique, so the proposed lower bound is 18. Interpretation follows the
catalogue's “unique maximum independent set” heading for u(G).
Lean 4.19.0, bundled standard library only. AI-assisted work for review;
no priority claim.
-/

import Std
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti138
universe u
variable {V : Type u} [DecidableEq V]

theorem choose_le_length (xs ys : List V) (R : V → V → Prop)
    (hnx : xs.Nodup) (hny : ys.Nodup)
    (h : ∀ x ∈ xs, ∃ y ∈ ys, R x y)
    (hu : ∀ x x' y, R x y → R x' y → x = x') : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    obtain ⟨y,hy,hay⟩ := h a (List.mem_cons_self ..)
    have htail := (List.nodup_cons.mp hnx)
    have next : ∀ x ∈ as, ∃ z ∈ ys.erase y, R x z := by
      intro x hx
      obtain ⟨z,hz,hxz⟩ := h x (List.mem_cons_of_mem _ hx)
      have hzy : z ≠ y := by
        intro e; subst z
        have e' := hu a x y hay hxz
        exact htail.1 (e' ▸ hx)
      exact ⟨z,(hny.mem_erase_iff).2 ⟨hzy,hz⟩,hxz⟩
    have ih' := ih (ys.erase y) htail.2 (hny.erase y) next
    rw [List.length_erase_of_mem hy] at ih'
    have hpos : 0 < ys.length := by
      cases ys with
      | nil => simp at hy
      | cons _ _ => simp
    simp only [List.length_cons]
    omega

theorem subset_le_length {xs ys : List V}
    (hnx : xs.Nodup) (hny : ys.Nodup) (h : xs ⊆ ys) : xs.length ≤ ys.length := by
  exact choose_le_length xs ys Eq hnx hny
    (fun x hx => ⟨x,h hx,rfl⟩) (fun _ _ _ u v => u.trans v.symm)

theorem count_filter_split (l : List V) (P Q : V → Bool) :
    (l.filter P).length = (l.filter (fun v => P v && Q v)).length
      + (l.filter (fun v => P v && !Q v)).length := by
  simpa only [List.countP_eq_length_filter, List.filter_filter] using
    List.countP_eq_countP_filter_add l P Q

theorem count_filter_comm (l : List V) (P Q : V → Bool) :
    (l.filter (fun v => P v && Q v)).length = (l.filter (fun v => Q v && P v)).length := by
  simp [Bool.and_comm]

theorem filter_nodup {xs : List V} (h : xs.Nodup) (P : V → Bool) :
    (xs.filter P).Nodup := List.filter_sublist.nodup h

theorem two_members {xs : List V} (hd : xs.Nodup) (h : 2 ≤ xs.length) :
    ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y := by
  cases xs with
  | nil => simp at h
  | cons x tail =>
    cases tail with
    | nil => simp at h
    | cons y ys =>
      refine ⟨x,by simp,y,by simp,?_⟩
      intro e; subst y
      exact (List.nodup_cons.mp hd).1 (by simp)

theorem singleton_unique {xs : List V}
    (h : xs.length ≤ 1) {u v} (hu : u ∈ xs) (hv : v ∈ xs) : u = v := by
  cases xs with
  | nil => simp at hu
  | cons a tail =>
    cases tail with
    | nil =>
      have hu' : u = a := by simpa using hu
      have hv' : v = a := by simpa using hv
      exact hu'.trans hv'.symm
    | cons b bs => simp at h

theorem positive_member {xs : List V} (h : 0 < xs.length) : ∃ x, x ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons a tail => exact ⟨a,by simp⟩

theorem member_positive {xs : List V} {x : V} (h : x ∈ xs) : 0 < xs.length := by
  cases xs with
  | nil => simp at h
  | cons a tail => simp

abbrev Vertex := Fin 19

/-- The handle 0--1--...--14, with two private leaves at either end. -/
abbrev Adj (u v : Vertex) : Prop :=
  (u.val+1 = v.val ∧ v.val≤14) ∨ (v.val+1 = u.val ∧ u.val≤14) ∨
  (u.val=0 ∧ (v.val=15 ∨ v.val=16)) ∨ (v.val=0 ∧ (u.val=15 ∨ u.val=16)) ∨
  (u.val=14 ∧ (v.val=17 ∨ v.val=18)) ∨ (v.val=14 ∧ (u.val=17 ∨ u.val=18))

theorem adj_symm {u v : Vertex} (h : Adj u v) : Adj v u := by
  unfold Adj at *
  omega

theorem adj_loopless (u : Vertex) : ¬ Adj u u := by
  unfold Adj
  omega

abbrev SquareAdj (u v : Vertex) : Prop :=
  u ≠ v ∧ (Adj u v ∨ ∃ w : Vertex, Adj u w ∧ Adj w v)

theorem square_symm {u v : Vertex} (h : SquareAdj u v) : SquareAdj v u := by
  refine ⟨Ne.symm h.1,?_⟩
  rcases h.2 with e|⟨w,e,f⟩
  · exact Or.inl (adj_symm e)
  · exact Or.inr ⟨w,adj_symm f,adj_symm e⟩

inductive Walk (R : Vertex → Vertex → Prop) : Vertex → Vertex → Nat → Prop
  | nil {v} : Walk R v v 0
  | cons {u v w n} : R u v → Walk R v w n → Walk R u w (n+1)

theorem walk_append {R : Vertex → Vertex → Prop} {u v w n m}
    (h : Walk R u v n) (h' : Walk R v w m) : Walk R u w (n+m) := by
  induction h with
  | nil => simpa using h'
  | @cons a b c k e he ih =>
    have hw := Walk.cons e (ih h')
    rw [Nat.succ_add]
    exact hw

theorem walk_reverse {R : Vertex → Vertex → Prop}
    (hs : ∀ {u v}, R u v → R v u) {u v n} (h : Walk R u v n) :
    Walk R v u n := by
  induction h with
  | nil => exact .nil
  | cons e _ ih => exact walk_append ih (.cons (hs e) .nil)

theorem handle_to_zero (k : Nat) (hk : k≤14) : Walk Adj (⟨k,by omega⟩ : Vertex) 0 k := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    have hprev : k≤14 := by omega
    apply Walk.cons (v := ⟨k,by omega⟩)
    · unfold Adj
      exact Or.inr (Or.inl ⟨rfl,hk⟩)
    · exact ih hprev

theorem to_zero (u : Vertex) : ∃ n, Walk Adj u 0 n := by
  by_cases he : u.val≤14
  · exact ⟨u.val,handle_to_zero u.val he⟩
  · by_cases hm : u.val≤16
    · refine ⟨1,Walk.cons (v:=0) ?_ .nil⟩
      unfold Adj
      omega
    · refine ⟨15,Walk.cons (v:=14) ?_ (handle_to_zero 14 (by decide))⟩
      unfold Adj
      have hu := u.isLt
      omega

theorem connected : ∀ u v : Vertex, ∃ n, Walk Adj u v n := by
  intro u v
  obtain ⟨n,hu⟩ := to_zero u
  obtain ⟨m,hv⟩ := to_zero v
  exact ⟨n+m,walk_append hu (walk_reverse adj_symm hv)⟩

def coordinate (v : Vertex) : Nat :=
  if v.val≤14 then v.val else if v.val≤16 then 0 else 14

theorem edge_step {u v : Vertex} (h : Adj u v) : coordinate v ≤ coordinate u+1 := by
  unfold Adj at h
  unfold coordinate
  split <;> split <;> (try split) <;> (try split) <;> omega

theorem square_step {u v : Vertex} (h : SquareAdj u v) : coordinate v ≤ coordinate u+2 := by
  rcases h.2 with e|⟨w,e,f⟩
  · have h := edge_step e; omega
  · have h := edge_step e
    have h' := edge_step f
    omega

theorem walk_square_bound {u v : Vertex} {n : Nat} (h : Walk SquareAdj u v n) :
    coordinate v ≤ coordinate u + 2*n := by
  induction h with
  | nil => simp
  | @cons a b c k e h ih =>
    have q := square_step e
    omega

def cells : List (List Vertex) :=
  [[0,15],[14,17],[1,2],[3,4],[5,6],[7,8],[9,10],[11,12],[13],[16],[18]]

def verts : List Vertex := cells.flatten

set_option maxRecDepth 5000 in
theorem verts_nodup : verts.Nodup := by decide

theorem verts_complete : ∀ v : Vertex, v ∈ verts := by decide

theorem verts_size : verts.length = 19 := by decide

def cardinal (P : Vertex → Bool) : Nat := (verts.filter P).length
def Independent (P : Vertex → Bool) : Prop :=
  ∀ u v, P u=true → P v=true → ¬ Adj u v
def IsMaximumIndependent (P : Vertex → Bool) : Prop :=
  Independent P ∧ ∀ Q, Independent Q → cardinal Q ≤ cardinal P

def witness (v : Vertex) : Bool := decide ((v.val≤13 ∧ v.val%2=1) ∨ 15≤v.val)

theorem witness_indep : Independent witness := by
  intro u v hu hv h
  have hu' := of_decide_eq_true hu
  have hv' := of_decide_eq_true hv
  unfold Adj at h
  omega

theorem witness_card : cardinal witness = 11 := by decide

theorem cell_cliques : ∀ xs∈cells, ∀ u∈xs, ∀ v∈xs, u≠v → Adj u v := by decide

theorem cell_bound (P : Vertex → Bool) (hP : Independent P) {c : List Vertex}
    (hc : c∈cells) : (c.filter P).length ≤ 1 := by
  have hnd := verts_nodup
  have hcnd : c.Nodup := by
    apply List.Sublist.nodup _ hnd
    exact List.sublist_flatten_of_mem hc
  by_cases he : 2 ≤ (c.filter P).length
  · obtain ⟨u,hu,v,hv,hneq⟩ := two_members (filter_nodup hcnd P) he
    have hu' := List.mem_filter.mp hu
    have hv' := List.mem_filter.mp hv
    exact False.elim (hP _ _ hu'.2 hv'.2 (cell_cliques _ hc _ hu'.1 _ hv'.1 hneq))
  · omega

theorem cells_cardinality (P : Vertex → Bool) (cs : List (List Vertex)) :
    (cs.flatten.filter P).length = (cs.map (fun c => (c.filter P).length)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.flatten_cons,List.filter_append,List.length_append,List.map_cons,List.sum_cons,ih]

theorem sum_le_count {xs : List Nat} (h : ∀ x∈xs, x≤1) : xs.sum ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons,List.length_cons]
    omega

theorem sum_eq_mem_one {xs : List Nat} (h : ∀ x∈xs, x≤1)
    (he : xs.length ≤ xs.sum) : ∀ x∈xs, x=1 := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht (x) := fun hx : x∈as => h x (List.mem_cons_of_mem _ hx)
    have hs := sum_le_count ht
    simp only [List.sum_cons,List.length_cons] at he
    intro x hx
    rcases List.mem_cons.mp hx with e|e
    · omega
    · exact ih ht (by omega) x e

theorem blocks_le_11 (P : Vertex → Bool) (hP : Independent P) : cardinal P ≤ 11 := by
  let B := cells.map (fun c => (c.filter P).length)
  have hh : ∀ x∈B, x≤1 := by
    intro x hx
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
    exact cell_bound P hP hc
  have he : B.sum = cardinal P := (cells_cardinality P cells).symm
  have hlen : B.length=11 := by simp [B,cells]
  have hp := sum_le_count hh
  omega

theorem saturated (P : Vertex → Bool) (hP : Independent P) (nP : 11≤cardinal P)
    (c : List Vertex) (hc : c∈cells) : (c.filter P).length = 1 := by
  let B := cells.map (fun c => (c.filter P).length)
  have hh : ∀ x∈B, x≤1 := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact cell_bound P hP hq
  have he : B.sum = cardinal P := (cells_cardinality P cells).symm
  have hlen : B.length=11 := by simp [B,cells]
  have hm : (c.filter P).length ∈ B := List.mem_map.mpr ⟨c,hc,rfl⟩
  exact sum_eq_mem_one hh (by omega) _ hm

theorem one_in_single {P : Vertex → Bool} {v : Vertex}
    (h : ([v].filter P).length = 1) : P v=true := by
  cases hv : P v <;> simp [hv] at h ⊢

theorem one_in_pair {P : Vertex → Bool} {a b : Vertex}
    (h : ([a,b].filter P).length = 1) (hb : P b=false) : P a=true := by
  cases ha : P a <;> simp [ha,hb] at h ⊢

theorem one_in_pair' {P : Vertex → Bool} {a b : Vertex}
    (h : ([a,b].filter P).length = 1) (ha : P a=false) : P b=true := by
  cases hb : P b <;> simp [ha,hb] at h ⊢

theorem neighbor_not_selected {P : Vertex → Bool} (hP : Independent P)
    {u v : Vertex} (hu : P u=true) (h : Adj u v) : P v=false :=
  Bool.eq_false_iff.mpr (fun hv => hP _ _ hu hv h)

theorem witness_unique (P : Vertex → Bool) (hP : Independent P) (hn : 11≤cardinal P) :
    P = witness := by
  have s13 : P 13=true := one_in_single (saturated P hP hn [13] (by decide))
  have s16 : P 16=true := one_in_single (saturated P hP hn [16] (by decide))
  have s18 : P 18=true := one_in_single (saturated P hP hn [18] (by decide))
  have s0 : P 0=false := neighbor_not_selected hP s16 (by decide)
  have s14 : P 14=false := neighbor_not_selected hP s18 (by decide)
  have s15 : P 15=true := one_in_pair' (saturated P hP hn [0,15] (by decide)) s0
  have s17 : P 17=true := one_in_pair' (saturated P hP hn [14,17] (by decide)) s14
  have s12 : P 12=false := neighbor_not_selected hP s13 (by decide)
  have s11 : P 11=true := one_in_pair (saturated P hP hn [11,12] (by decide)) s12
  have s10 : P 10=false := neighbor_not_selected hP s11 (by decide)
  have s9 : P 9=true := one_in_pair (saturated P hP hn [9,10] (by decide)) s10
  have s8 : P 8=false := neighbor_not_selected hP s9 (by decide)
  have s7 : P 7=true := one_in_pair (saturated P hP hn [7,8] (by decide)) s8
  have s6 : P 6=false := neighbor_not_selected hP s7 (by decide)
  have s5 : P 5=true := one_in_pair (saturated P hP hn [5,6] (by decide)) s6
  have s4 : P 4=false := neighbor_not_selected hP s5 (by decide)
  have s3 : P 3=true := one_in_pair (saturated P hP hn [3,4] (by decide)) s4
  have s2 : P 2=false := neighbor_not_selected hP s3 (by decide)
  have s1 : P 1=true := one_in_pair (saturated P hP hn [1,2] (by decide)) s2
  funext v
  have hv : v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 ∨ v.val=4 ∨ v.val=5 ∨ v.val=6 ∨ v.val=7 ∨ v.val=8 ∨ v.val=9 ∨ v.val=10 ∨ v.val=11 ∨ v.val=12 ∨ v.val=13 ∨ v.val=14 ∨ v.val=15 ∨ v.val=16 ∨ v.val=17 ∨ v.val=18 := by omega
  rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have he : v=0 := Fin.ext h
    subst v
    exact s0
  · have he : v=1 := Fin.ext h
    subst v
    exact s1
  · have he : v=2 := Fin.ext h
    subst v
    exact s2
  · have he : v=3 := Fin.ext h
    subst v
    exact s3
  · have he : v=4 := Fin.ext h
    subst v
    exact s4
  · have he : v=5 := Fin.ext h
    subst v
    exact s5
  · have he : v=6 := Fin.ext h
    subst v
    exact s6
  · have he : v=7 := Fin.ext h
    subst v
    exact s7
  · have he : v=8 := Fin.ext h
    subst v
    exact s8
  · have he : v=9 := Fin.ext h
    subst v
    exact s9
  · have he : v=10 := Fin.ext h
    subst v
    exact s10
  · have he : v=11 := Fin.ext h
    subst v
    exact s11
  · have he : v=12 := Fin.ext h
    subst v
    exact s12
  · have he : v=13 := Fin.ext h
    subst v
    exact s13
  · have he : v=14 := Fin.ext h
    subst v
    exact s14
  · have he : v=15 := Fin.ext h
    subst v
    exact s15
  · have he : v=16 := Fin.ext h
    subst v
    exact s16
  · have he : v=17 := Fin.ext h
    subst v
    exact s17
  · have he : v=18 := Fin.ext h
    subst v
    exact s18

theorem unique_maximum : ∃ P : Vertex → Bool, IsMaximumIndependent P ∧
    ∀ Q, IsMaximumIndependent Q → Q=P := by
  refine ⟨witness, ⟨witness_indep,?_⟩,?_⟩
  · intro Q hQ
    rw [witness_card]
    exact blocks_le_11 Q hQ
  · intro Q hQ
    apply witness_unique Q hQ.1
    simpa only [witness_card] using hQ.2 witness witness_indep


abbrev IsLeaf (v : Vertex) : Prop := 15 ≤ v.val
abbrev leafFilter (v : Vertex) : Bool := decide (IsLeaf v)

theorem leaf_neighbours_unique {v a b : Vertex} (hv : IsLeaf v)
    (ha : Adj v a) (hb : Adj v b) : a=b := by
  apply Fin.ext
  unfold Adj at ha hb
  omega

def Consecutive : List Vertex → Prop
  | a::b::xs => Adj a b ∧ Consecutive (b::xs)
  | _ => True

instance instDecConsecutive (l : List Vertex) : Decidable (Consecutive l) :=
  match l with
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a::b::xs =>
    let _ : Decidable (Consecutive (b::xs)) := instDecConsecutive (b::xs)
    inferInstanceAs (Decidable (Adj a b ∧ Consecutive (b::xs)))

def NoChord (l : List Vertex) : Prop :=
  ∀ i j : Fin l.length, i.val+1 < j.val → ¬ Adj (l.get i) (l.get j)

def InducedPath (l : List Vertex) : Prop :=
  0<l.length ∧ l.Nodup ∧ Consecutive l ∧ NoChord l

theorem path_tail_leaf_count (l : List Vertex) (a : Vertex)
    (hc : Consecutive (a::l)) (hn : (a::l).Nodup) :
    (l.filter leafFilter).length ≤ 1 := by
  induction l generalizing a with
  | nil => simp
  | cons b tail ih =>
    cases tail with
    | nil => exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    | cons c rest =>
      have hne : a≠c := by
        intro he
        subst c
        exact (List.nodup_cons.mp hn).1 (by simp)
      have hae : Adj a b := hc.1
      have hce : Adj b c := hc.2.1
      have hb : ¬ IsLeaf b := by
        intro h
        exact hne (leaf_neighbours_unique h (adj_symm hae) hce)
      have htail := ih b hc.2 (List.nodup_cons.mp hn).2
      simpa [hb] using htail

theorem path_order_bound (l : List Vertex) (hc : Consecutive l) (hn : l.Nodup) :
    l.length ≤ 17 := by
  have hLeaves : (l.filter leafFilter).length ≤ 2 := by
    cases l with
    | nil => simp
    | cons a as =>
      have ht := path_tail_leaf_count as a hc hn
      simp only [List.filter_cons]
      split <;> simp at * <;> omega
  have hHandle : (l.filter (fun v => !leafFilter v)).length ≤ 15 := by
    let H : List Vertex := verts.filter (fun v => !leafFilter v)
    have hs : (l.filter (fun v => !leafFilter v)) ⊆ H := by
      intro v hv
      have hv' := List.mem_filter.mp hv
      exact List.mem_filter.mpr ⟨verts_complete v,hv'.2⟩
    have hb := subset_le_length (filter_nodup hn _) (filter_nodup verts_nodup _) hs
    have hCard : H.length=15 := by decide
    change (l.filter (fun v => !leafFilter v)).length ≤ H.length at hb
    omega
  have hC : l.length = (l.filter leafFilter).length + (l.filter (fun v => !leafFilter v)).length := by
    have hs := count_filter_split l (fun _ => true) leafFilter
    have he : l.filter (fun _ => true) = l := by simp
    rw [he] at hs
    simpa only [Bool.true_and] using hs
  omega

def longestWitness : List Vertex := [15,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,17]

set_option maxRecDepth 5000 in
theorem path_order_exact_witness : InducedPath longestWitness ∧ longestWitness.length=17 := by
  refine ⟨⟨by decide,by decide,by decide,?_⟩,by decide⟩
  unfold NoChord
  decide

instance squareDec (a b : Vertex) : Decidable (SquareAdj a b) := by
  let test : Vertex → Bool := fun w => decide (Adj a w ∧ Adj w b)
  have he : verts.any test = true ↔ ∃ w : Vertex, Adj a w ∧ Adj w b := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨w,_,hw⟩
      exact ⟨w,of_decide_eq_true hw⟩
    · rintro ⟨w,hw⟩
      exact ⟨w,verts_complete w,decide_eq_true hw⟩
  exact decidable_of_iff (a ≠ b ∧ (Adj a b ∨ verts.any test = true))
    (and_congr_right (fun _ => or_congr_right he))

def degree2 (v : Vertex) : Nat := cardinal (fun w => decide (SquareAdj v w))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem square_deg_certificate (v : Vertex) :
    degree2 v = (if v.val=1 ∨ v.val=13 then 5 else if v.val≤14 then 4 else 3) := by
  have hv : v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 ∨ v.val=4 ∨ v.val=5 ∨ v.val=6 ∨ 
    v.val=7 ∨ v.val=8 ∨ v.val=9 ∨ v.val=10 ∨ v.val=11 ∨ v.val=12 ∨ v.val=13 ∨ v.val=14 ∨ 
    v.val=15 ∨ v.val=16 ∨ v.val=17 ∨ v.val=18 := by omega
  rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have he : v=0 := Fin.ext h
    subst v
    decide
  · have he : v=1 := Fin.ext h
    subst v
    decide
  · have he : v=2 := Fin.ext h
    subst v
    decide
  · have he : v=3 := Fin.ext h
    subst v
    decide
  · have he : v=4 := Fin.ext h
    subst v
    decide
  · have he : v=5 := Fin.ext h
    subst v
    decide
  · have he : v=6 := Fin.ext h
    subst v
    decide
  · have he : v=7 := Fin.ext h
    subst v
    decide
  · have he : v=8 := Fin.ext h
    subst v
    decide
  · have he : v=9 := Fin.ext h
    subst v
    decide
  · have he : v=10 := Fin.ext h
    subst v
    decide
  · have he : v=11 := Fin.ext h
    subst v
    decide
  · have he : v=12 := Fin.ext h
    subst v
    decide
  · have he : v=13 := Fin.ext h
    subst v
    decide
  · have he : v=14 := Fin.ext h
    subst v
    decide
  · have he : v=15 := Fin.ext h
    subst v
    decide
  · have he : v=16 := Fin.ext h
    subst v
    decide
  · have he : v=17 := Fin.ext h
    subst v
    decide
  · have he : v=18 := Fin.ext h
    subst v
    decide

def MaximumSquareDegree (v : Vertex) : Prop := ∀ w, degree2 w ≤ degree2 v

theorem max_square_deg_set {v : Vertex} :
    MaximumSquareDegree v ↔ v=1 ∨ v=13 := by
  constructor
  · intro h
    have ht := h 1
    rw [square_deg_certificate, square_deg_certificate] at ht
    have hcalc : (if (1 : Vertex).val=1 ∨ (1 : Vertex).val=13 then 5 else if (1 : Vertex).val≤14 then 4 else 3)=5 := by decide
    rw [hcalc] at ht
    split at ht
    · rcases ‹v.val=1 ∨ v.val=13› with hv|hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    · split at ht <;> omega
  · intro h w
    rw [square_deg_certificate, square_deg_certificate]
    rcases h with e|e
    · subst v
      have hcalc : (if (1 : Vertex).val=1 ∨ (1 : Vertex).val=13 then 5 else if (1 : Vertex).val≤14 then 4 else 3)=5 := by decide
      rw [hcalc]
      split <;> (try split) <;> omega
    · subst v
      have hcalc : (if (13 : Vertex).val=1 ∨ (13 : Vertex).val=13 then 5 else if (13 : Vertex).val≤14 then 4 else 3)=5 := by decide
      rw [hcalc]
      split <;> (try split) <;> omega

def SquareDistance (a b : Vertex) (d : Nat) : Prop :=
  Walk SquareAdj a b d ∧ ∀ k, Walk SquareAdj a b k → d≤k

theorem sqdist_1_13 : SquareDistance 1 13 6 := by
  constructor
  · exact Walk.cons (v:=3) (by decide)
      (Walk.cons (v:=5) (by decide)
      (Walk.cons (v:=7) (by decide)
      (Walk.cons (v:=9) (by decide)
      (Walk.cons (v:=11) (by decide)
      (Walk.cons (by decide) .nil)))))
  · intro k h
    have hb := walk_square_bound h
    have h1 : coordinate 1 = 1 := by decide
    have h2 : coordinate 13 = 13 := by decide
    rw [h1,h2] at hb
    omega

theorem sqdist_symm {a b : Vertex} {d : Nat} (h : SquareDistance a b d) :
    SquareDistance b a d :=
  ⟨walk_reverse square_symm h.1,fun k hk => h.2 k (walk_reverse square_symm hk)⟩

def IsMinMaxSquareDistance (d : Nat) : Prop :=
    (∃ a b, a≠b ∧ MaximumSquareDegree a ∧ MaximumSquareDegree b ∧ SquareDistance a b d) ∧
    ∀ a b k, a≠b → MaximumSquareDegree a → MaximumSquareDegree b →
      SquareDistance a b k → d≤k

theorem min_max_distance : IsMinMaxSquareDistance 6 := by
  constructor
  · exact ⟨1,13,by decide,max_square_deg_set.mpr (Or.inl rfl),
      max_square_deg_set.mpr (Or.inr rfl),sqdist_1_13⟩
  · intro a b k hab ha hb hk
    rcases max_square_deg_set.mp ha with e|e <;> rcases max_square_deg_set.mp hb with f|f <;>
      subst a <;> subst b
    · exact False.elim (hab rfl)
    · exact sqdist_1_13.2 k hk.1
    · exact (sqdist_symm sqdist_1_13).2 k hk.1
    · exact False.elim (hab rfl)

/-- The maximum induced-path order, with existence and exactness witnessed. -/
def IsPathNumber (n : Nat) : Prop :=
  (∃ l, InducedPath l ∧ l.length=n) ∧ ∀ l, InducedPath l → l.length≤n

theorem path_number : IsPathNumber 17 :=
  ⟨⟨_,path_order_exact_witness.1,path_order_exact_witness.2⟩,
    fun l h => path_order_bound l h.2.2.1 h.2.1⟩

theorem path_number_unique {m n : Nat} (hm : IsPathNumber m) (hn : IsPathNumber n) : m=n := by
  obtain ⟨l,hl,hm'⟩ := hm.1
  obtain ⟨l',hl',hn'⟩ := hn.1
  have ha := hn.2 l hl
  have hb := hm.2 l' hl'
  omega

theorem square_min_unique {m n : Nat} (hm : IsMinMaxSquareDistance m)
    (hn : IsMinMaxSquareDistance n) : m=n := by
  obtain ⟨a,b,hab,ha,hb,hm'⟩ := hm.1
  obtain ⟨c,d,hcd,hc,hd,hn'⟩ := hn.1
  exact Nat.le_antisymm (hm.2 _ _ _ hcd hc hd hn') (hn.2 _ _ _ hab ha hb hm')

noncomputable def characteristic : Nat := by
  classical
  exact if (∃ P : Vertex → Bool, IsMaximumIndependent P ∧
    ∀ Q, IsMaximumIndependent Q → Q=P) then 1 else 0

theorem characteristic_one : characteristic=1 := by
  unfold characteristic
  exact if_pos unique_maximum

/-- Literal source inequality on the explicit graph, using the square-graph
metric and the exact graph invariants. -/
def SourceBound : Prop :=
  ∃ n d, IsPathNumber n ∧ IsMinMaxSquareDistance d ∧ (2+characteristic)*d ≤ n

theorem conjecture138_is_false : ¬ SourceBound := by
  intro h
  obtain ⟨n,d,hn,hd,hbad⟩ := h
  have en := path_number_unique hn path_number
  have ed := square_min_unique hd min_max_distance
  rw [en,ed,characteristic_one] at hbad
  omega

theorem counterexample138 :
    (∀ u v : Vertex, ∃ n, Walk Adj u v n) ∧
      (∀ u v, Adj u v → Adj v u) ∧ (∀ u, ¬ Adj u u) ∧
      IsPathNumber 17 ∧ IsMinMaxSquareDistance 6 ∧ characteristic=1 ∧ ¬ SourceBound :=
  ⟨connected,fun _ _ h => adj_symm h,adj_loopless,path_number,min_max_distance,
    characteristic_one,conjecture138_is_false⟩

#print axioms counterexample138
end Graffiti138
