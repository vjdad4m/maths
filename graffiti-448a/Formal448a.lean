import Std
set_option warningAsError true

namespace Graffiti449

def sumMap {V : Type} (l : List V) (f : V → Nat) : Nat :=
  (l.map f).sum

theorem sumMapMono {V : Type} (l : List V) (f g : V → Nat)
    (h : ∀ u ∈ l, f u ≤ g u) : sumMap l f ≤ sumMap l g := by
  induction l with
  | nil => simp [sumMap]
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun u hu => h u (by simp [hu]))
    simp only [sumMap, List.map_cons, List.sum_cons] at *
    omega

theorem sumMapAdd {V : Type} (l : List V) (f g : V → Nat) :
    sumMap l (fun u => f u+g u) = sumMap l f + sumMap l g := by
  induction l with
  | nil => simp [sumMap]
  | cons a l ih =>
    simp only [sumMap, List.map_cons, List.sum_cons] at *
    omega

theorem sumMapDouble {V : Type} (l : List V) (f : V → Nat) :
    sumMap l (fun u => 2*f u) = 2*sumMap l f := by
  have h := sumMapAdd l f f
  simpa only [Nat.two_mul] using h

theorem sumMapSwap {V : Type} (l m : List V) (f : V → V → Nat) :
    sumMap l (fun x => sumMap m (f x)) =
    sumMap m (fun y => sumMap l (fun x => f x y)) := by
  induction l with
  | nil =>
    have h : sumMap m (fun _ => 0) = 0 := by
      induction m with
      | nil => rfl
      | cons a m ih => simpa [sumMap] using ih
    simpa [sumMap] using h.symm
  | cons x l ih =>
    change sumMap m (f x) + sumMap l (fun x => sumMap m (f x)) = _
    rw [ih, ← sumMapAdd]
    rfl

abbrev Graph (n : Nat) := Fin n → Fin n → Bool
abbrev Subset (n : Nat) := Fin n → Bool

def verts (n : Nat) : List (Fin n) := List.ofFn id
def bit (b : Bool) : Nat := if b then 1 else 0

def card {n} (I : Subset n) : Nat := sumMap (verts n) (fun u => bit (I u))
def degree {n} (G : Graph n) (u : Fin n) : Nat := card (G u)
def high {n} (G : Graph n) : Subset n := fun u => decide (3 ≤ degree G u)
def low {n} (G : Graph n) : Subset n := fun u => !high G u

def pairCount {n} (G : Graph n) (P Q : Subset n) : Nat :=
  sumMap (verts n) (fun u => sumMap (verts n) (fun v => bit (P u && Q v && G u v)))

def localCount {n} (G : Graph n) (I : Subset n) (u : Fin n) : Nat :=
  card (fun v => I v && G u v)

theorem cardSplit {n} (P Q : Subset n) :
    card P = card (fun u => P u && Q u) + card (fun u => P u && !Q u) := by
  unfold card
  rw [← sumMapAdd]
  unfold sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  cases hp : P u <;> cases hq : Q u <;> simp [hp, hq, bit]

theorem pairSwap {n} (G : Graph n) (hs : ∀ u v, G u v = G v u) (P Q : Subset n) :
    pairCount G P Q = pairCount G Q P := by
  unfold pairCount
  rw [sumMapSwap]
  unfold sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  congr 1
  apply List.map_congr_left
  intro v _
  rw [hs v u, Bool.and_comm (P v) (Q u)]

theorem pairSplit {n} (G : Graph n) (P Q R : Subset n) :
    pairCount G P Q = pairCount G P (fun u => Q u && R u) + pairCount G P (fun u => Q u && !R u) := by
  unfold pairCount
  rw [← sumMapAdd]
  unfold sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  have h := sumMapAdd (verts n)
    (fun v => bit (P u && (Q v && R v) && G u v))
    (fun v => bit (P u && (Q v && !R v) && G u v))
  unfold sumMap at h
  rw [← h]
  congr 1
  apply List.map_congr_left
  intro v _
  cases P u <;> cases Q v <;> cases R v <;> cases G u v <;> rfl

theorem pairMono {n} (G : Graph n) (P Q P' Q' : Subset n)
    (hp : ∀ u, P u = true → P' u = true) (hq : ∀ u, Q u = true → Q' u = true) :
    pairCount G P Q ≤ pairCount G P' Q' := by
  unfold pairCount
  apply sumMapMono
  intro u _
  apply sumMapMono
  intro v _
  cases he : P u && Q v && G u v with
  | false => exact Nat.zero_le _
  | true =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at he
    simp [hp u he.1.1, hq v he.1.2, he.2, bit]

theorem pairRows {n} (G : Graph n) (P Q : Subset n) :
    pairCount G P Q = sumMap (verts n) (fun u => if P u then localCount G Q u else 0) := by
  unfold pairCount sumMap
  congr 1
  apply List.map_congr_left
  intro u _
  cases hu : P u
  · simp only [hu, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bit]
    induction (verts n) with
    | nil => rfl
    | cons a l ih => simp [ih]
  · simp [hu, localCount, card, sumMap]

theorem degreeSplit {n} (G : Graph n) (I : Subset n) (u : Fin n) :
    degree G u = localCount G I u + localCount G (fun u => !I u) u := by
  have h := cardSplit (G u) I
  simpa [degree, localCount, Bool.and_comm] using h

def TwoIndependent {n} (G : Graph n) (I : Subset n) : Prop :=
  ∀ u, I u = true → localCount G I u ≤ 1

/-- In a symmetric loopless graph, each induced edge has exactly the two
orientations counted by pairCount; division by two gives its cardinality. -/
def inducedEdges {n} (G : Graph n) (I : Subset n) : Nat :=
  pairCount G I I / 2

theorem conjecture449_bound {n} (G : Graph n) (hs : ∀ u v, G u v = G v u)
    (I : Subset n) (hi : TwoIndependent G I) :
    card I ≤ card (low G) + inducedEdges G (high G) / 2 := by
  let H := high G
  let L := low G
  let A : Subset n := fun u => H u && I u
  let B : Subset n := fun u => L u && !I u
  let C : Subset n := fun u => H u && !I u
  let U : Subset n := fun u => !I u
  have hlo : ∀ u, L u = !H u := fun _ => rfl
  have hHi (u : Fin n) (h : A u = true) : 3 ≤ degree G u := by
    have hH : H u = true := (Bool.and_eq_true _ _).mp h |>.1
    simpa [H, high] using hH
  have hl (u : Fin n) (h : B u = true) : degree G u ≤ 2 := by
    have hL : L u = true := (Bool.and_eq_true _ _).mp h |>.1
    have hlt : ¬ 3 ≤ degree G u := by simpa [L, low, high] using hL
    omega
  have first : 2*card A ≤ pairCount G A U := by
    unfold card
    rw [← sumMapDouble, pairRows]
    apply sumMapMono
    intro u _
    cases h : A u
    · simp [h, bit]
    · have hu : I u = true := (Bool.and_eq_true _ _).mp h |>.2
      have hdeg := hHi u h
      have hsel := hi u hu
      have hd := degreeSplit G I u
      change degree G u = localCount G I u + localCount G U u at hd
      simp [h, bit]
      omega
  have second : pairCount G A B ≤ 2*card B := by
    rw [pairSwap G hs A B]
    unfold card
    rw [← sumMapDouble, pairRows]
    apply sumMapMono
    intro u _
    cases h : B u
    · simp [h, bit]
    · have hd := hl u h
      have hm : localCount G A u ≤ degree G u := by
        unfold localCount degree card
        apply sumMapMono
        intro v _
        cases hv : A v <;> cases hg : G u v <;> simp [hv, hg, bit]
      simp [h, bit]
      omega
  have hparts : pairCount G A U = pairCount G A C + pairCount G A B := by
    have h := pairSplit G A U H
    simpa [C, B, L, low, U, H, Bool.and_comm] using h
  have htwice : 2*pairCount G A C ≤ pairCount G H H := by
    have h := pairSplit G H H I
    change pairCount G H H = pairCount G H A + pairCount G H C at h
    have hA : ∀ u, A u = true → H u = true :=
      fun u hu => (Bool.and_eq_true _ _).mp hu |>.1
    have hC : ∀ u, C u = true → H u = true :=
      fun u hu => (Bool.and_eq_true _ _).mp hu |>.1
    have h1 := pairMono G C A H A hC (fun _ h => h)
    have h2 := pairMono G A C H C hA (fun _ h => h)
    rw [pairSwap G hs C A] at h1
    omega
  have hcross : pairCount G A C ≤ inducedEdges G H := by
    unfold inducedEdges
    omega
  have hselec := cardSplit I H
  have hlow := cardSplit L I
  have hA : card (fun u => I u && H u) = card A := by simp [A, Bool.and_comm]
  have hB : card (fun u => L u && !I u) = card B := rfl
  have hC : card (fun u => I u && !H u) = card (fun u => L u && I u) := by
    simp [L, low, H, Bool.and_comm]
  rw [hA,hC] at hselec
  rw [hB] at hlow
  change card I ≤ card L + inducedEdges G H / 2
  omega


def Attainable {n} (G : Graph n) (k : Nat) : Prop :=
  ∃ I, TwoIndependent G I ∧ card I = k

theorem attainedEmpty {n} (G : Graph n) : Attainable G 0 := by
  refine ⟨fun _ => false, fun _ h => Bool.noConfusion h, ?_⟩
  unfold card
  induction (verts n) with
  | nil => rfl
  | cons a l ih => simp [sumMap, bit] at *; exact ih

theorem cardLeOrder {n} (I : Subset n) : card I ≤ n := by
  have h : sumMap (verts n) (fun _ => 1) = n := by
    have hl : ∀ l : List (Fin n), sumMap l (fun _ => 1) = l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [sumMap, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
    simpa [verts] using hl (verts n)
  calc
    card I ≤ sumMap (verts n) (fun _ => 1) := sumMapMono _ _ _ (fun u _ => by cases I u <;> decide)
    _ = n := h

theorem maxNatExists (P : Nat → Prop) (bound : Nat)
    (h0 : P 0) (hb : ∀ k, P k → k ≤ bound) :
    ∃ k, P k ∧ ∀ j, P j → j ≤ k := by
  classical
  induction bound with
  | zero => exact ⟨0, h0, hb⟩
  | succ m ih =>
    by_cases h : P (m+1)
    · exact ⟨m+1,h,hb⟩
    · apply ih
      intro k hk
      have hkm := hb k hk
      have hneq : k ≠ m+1 := fun e => h (e ▸ hk)
      omega

/-- Exactly the maximum size of an induced subgraph of maximum degree one. -/
noncomputable def twoIndependenceNumber {n} (G : Graph n) : Nat :=
  Classical.choose <| maxNatExists (Attainable G) n (attainedEmpty G)
    (fun _ ⟨I, _, e⟩ => e ▸ cardLeOrder I)

/-- Catalogue #449; floor(m/2) equals ceiling((m−1)/2) for integral m≥0.
The no-loop condition is unnecessary for the stronger directed-count inequality. -/
theorem conjecture449 {n} (G : Graph n) (hs : ∀ u v, G u v = G v u) :
    twoIndependenceNumber G ≤ card (low G) + inducedEdges G (high G) / 2 := by
  obtain ⟨I, hI, hcard⟩ := (Classical.choose_spec (maxNatExists (Attainable G) n (attainedEmpty G)
    (fun _ ⟨I, _, e⟩ => e ▸ cardLeOrder I))).1
  change card I = twoIndependenceNumber G at hcard
  rw [← hcard]
  exact conjecture449_bound G hs I hI

#print axioms conjecture449
end Graffiti449

set_option warningAsError true
namespace Graffiti448a
open Graffiti449

def highHalf {n} (G : Graph n) : Subset n := fun u => decide (n/2 < degree G u)
def lowHalf {n} (G : Graph n) : Subset n := fun u => !highHalf G u

def Path {n} (G : Graph n) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => G u v = true ∧ Path G (v :: rest)

def PathCover {n} (G : Graph n) (P : List (List (Fin n))) : Prop :=
  P.flatten.Perm (verts n) ∧ ∀ p ∈ P, p ≠ [] ∧ Path G p

def canon {n} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u,v) else (v,u)

def lowEdges {n} (J : Subset n) : List (Fin n) → List (Fin n × Fin n)
  | [] => []
  | [_] => []
  | u :: v :: rest =>
      if J u && J v then canon u v :: lowEdges J (v :: rest)
      else lowEdges J (v :: rest)

def edgesOn {n} (G : Graph n) (J : Subset n) : List (Fin n × Fin n) :=
  (verts n).flatMap (fun a => ((verts n).filter
    (fun b => decide (a < b) && J a && J b && G a b)).map (fun b => (a,b)))

theorem allVerts {n} (v : Fin n) : v ∈ verts n := by
  simp [verts, List.mem_ofFn]

theorem nodupVerts (n) : (verts n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij h
  simp [verts, List.getElem_ofFn] at h
  omega

theorem filter_split_length {V : Type} (S : List V) (p : V → Bool) :
    S.length = (S.filter p).length + (S.filter (fun u => !p u)).length := by
  induction S with
  | nil => rfl
  | cons u us ih =>
    cases h : p u <;> simp [h] <;> omega

theorem sum_bits {V : Type} (S : List V) (p : V → Bool) :
    sumMap S (fun u => bit (p u)) = (S.filter p).length := by
  induction S with
  | nil => rfl
  | cons u us ih =>
    change bit (p u) + sumMap us (fun u => bit (p u)) = ((u::us).filter p).length
    rw [ih]
    cases h : p u <;> simp [h, bit, Nat.add_comm]

theorem path_count {n} (J : Subset n) (P : List (Fin n)) :
    (P.filter J).length ≤ (P.filter (fun u => !J u)).length + (lowEdges J P).length +
      ((P.head?).map (fun u => bit (J u))).getD 0 := by
  match P with
  | [] => simp [lowEdges]
  | [u] => cases h : J u <;> simp [h, lowEdges, bit]
  | u::v::tail =>
    have ih := path_count J (v::tail)
    cases hu : J u <;> cases hv : J v <;>
      simp [hu, hv, lowEdges, bit] at ih ⊢ <;> omega

theorem cover_count {n} (J : Subset n) (P : List (List (Fin n))) :
    (P.flatten.filter J).length ≤ (P.flatten.filter (fun u => !J u)).length +
      (P.flatMap (lowEdges J)).length + P.length := by
  induction P with
  | nil => simp
  | cons p ps ih =>
    have hp := path_count J p
    have hx : ((p.head?).map (fun u => bit (J u))).getD 0 ≤ 1 := by
      cases p with
      | nil => simp
      | cons u tail => cases h : J u <;> simp [h, bit]
    simp only [List.flatten_cons, List.flatMap_cons, List.filter_append, List.length_append, List.length_cons]
    omega

theorem lowEnds {n} (J : Subset n) (P : List (Fin n)) {e : Fin n × Fin n}
    (he : e ∈ lowEdges J P) : e.1 ∈ P ∧ e.2 ∈ P := by
  match P with
  | [] => simp [lowEdges] at he
  | [_] => simp [lowEdges] at he
  | u::v::tail =>
    cases h : J u && J v
    · have hh : e ∈ lowEdges J (v::tail) := by simpa [lowEdges,h] using he
      exact ⟨List.mem_cons_of_mem _ (lowEnds J (v::tail) hh).1,
        List.mem_cons_of_mem _ (lowEnds J (v::tail) hh).2⟩
    · have hh : e = canon u v ∨ e ∈ lowEdges J (v::tail) := by
        simpa [lowEdges,h] using he
      rcases hh with rfl | hh
      · unfold canon; split <;> simp
      · exact ⟨List.mem_cons_of_mem _ (lowEnds J (v::tail) hh).1,
          List.mem_cons_of_mem _ (lowEnds J (v::tail) hh).2⟩

theorem lowEdgesNodup {n} (J : Subset n) (P : List (Fin n)) (hP : P.Nodup) :
    (lowEdges J P).Nodup := by
  match P with
  | [] => exact List.nodup_nil
  | [_] => exact List.nodup_nil
  | u::v::tail =>
    have ⟨hU,hT⟩ := List.nodup_cons.mp hP
    have ih := lowEdgesNodup J (v::tail) hT
    cases h : J u && J v
    · simpa [lowEdges,h] using ih
    · rw [lowEdges, h]
      apply List.nodup_cons.mpr
      refine ⟨?_,ih⟩
      intro hm
      have he := lowEnds J (v::tail) hm
      apply hU
      unfold canon at he
      split at he
      · exact he.1
      · exact he.2

theorem coverEdgesNodup {n} (J : Subset n) (P : List (List (Fin n)))
    (hp : P.flatten.Nodup) : (P.flatMap (lowEdges J)).Nodup := by
  have h := List.pairwise_flatten.mp hp
  apply List.pairwise_flatMap.mpr
  refine ⟨fun p hm => lowEdgesNodup J p (h.1 p hm), ?_⟩
  apply h.2.imp
  intro p q sep x hx y hy eq
  subst y
  exact sep x.1 (lowEnds J p hx).1 x.1 (lowEnds J q hy).1 rfl

theorem canon_mem {n} (G : Graph n) (hs : ∀ u v, G u v = G v u)
    (J : Subset n) {u v} (hu : J u = true) (hv : J v = true)
    (h : G u v = true) (hne : u ≠ v) : canon u v ∈ edgesOn G J := by
  unfold canon
  simp only [edgesOn, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Bool.and_eq_true, allVerts, true_and, Prod.mk.injEq]
  split
  · rename_i hlt
    exact ⟨u,v,⟨⟨⟨hlt,hu⟩,hv⟩,h⟩,rfl⟩
  · rename_i hge
    have hlt : v < u := by
      have hn : u.val ≠ v.val := fun e => hne (Fin.ext e)
      change ¬ u.val < v.val at hge
      change v.val < u.val
      omega
    exact ⟨v,u,⟨⟨⟨hlt,hv⟩,hu⟩,(hs v u).trans h⟩,rfl⟩

theorem lowEdgesSubset {n} (G : Graph n) (hs : ∀ u v, G u v = G v u)
    (J : Subset n) (P : List (Fin n)) (hp : Path G P) (hd : P.Nodup) :
    ∀ e ∈ lowEdges J P, e ∈ edgesOn G J := by
  match P with
  | [] => simp [lowEdges]
  | [_] => simp [lowEdges]
  | u::v::tail =>
    have hp' : G u v = true ∧ Path G (v::tail) := hp
    have ⟨hu,ht⟩ := List.nodup_cons.mp hd
    intro e he
    cases h : J u && J v
    · have hh : e ∈ lowEdges J (v::tail) := by simpa [lowEdges,h] using he
      exact lowEdgesSubset G hs J (v::tail) hp'.2 ht _ hh
    · have hh : e = canon u v ∨ e ∈ lowEdges J (v::tail) := by
        simpa [lowEdges,h] using he
      rcases hh with rfl | hh
      · have hc := Bool.and_eq_true_iff.mp h
        exact canon_mem G hs J hc.1 hc.2 hp'.1 (by intro e; subst v; exact hu (by simp))
      · exact lowEdgesSubset G hs J (v::tail) hp'.2 ht _ hh

theorem length_subset {α : Type} [BEq α] [LawfulBEq α] (a b : List α)
    (ha : a.Nodup) (h : ∀ e ∈ a, e ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons u us ih =>
    obtain ⟨hn,hud⟩ := List.nodup_cons.mp ha
    have hub := h u (by simp)
    have hm : ∀ e ∈ us, e ∈ b.erase u := by
      intro e he
      have heb := h e (by simp [he])
      have neq : e ≠ u := fun eq => hn (eq ▸ he)
      exact (List.mem_erase_of_ne neq).mpr heb
    have h₂ := ih (b.erase u) hud hm
    have hb : 0 < b.length := List.length_pos_of_mem hub
    rw [List.length_erase_of_mem hub] at h₂
    simp only [List.length_cons]
    omega

/-- This enumeration contains exactly the canonical representatives of
the unordered edges in the subgraph induced by J. -/
theorem edgesOnExact {n} (G : Graph n) (J : Subset n) (a b : Fin n) :
    (a,b) ∈ edgesOn G J ↔ a < b ∧ J a = true ∧ J b = true ∧ G a b = true := by
  unfold edgesOn
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, allVerts, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨u,v,⟨⟨⟨h₁,h₂⟩,h₃⟩,h₄⟩,he⟩
    rcases he with ⟨hA,hB⟩
    subst a; subst b
    exact ⟨h₁,h₂,h₃,h₄⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨a,b,⟨⟨⟨h₁,h₂⟩,h₃⟩,h₄⟩,rfl,rfl⟩

theorem edgesOnNodup {n} (G : Graph n) (J : Subset n) : (edgesOn G J).Nodup := by
  unfold edgesOn
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro a _
    exact List.Pairwise.map (fun b => (a,b))
      (fun _ _ (h : _ ≠ _) eq => h (congrArg Prod.snd eq))
      (List.Pairwise.filter _ (nodupVerts n))
  · apply (nodupVerts n).imp
    intro a b hab p hp q hq h
    obtain ⟨u,_,he⟩ := List.mem_map.mp hp
    obtain ⟨v,_,hf⟩ := List.mem_map.mp hq
    rw [← he, ← hf] at h
    exact hab (congrArg Prod.fst h)

theorem coverEdgeBound {n} (G : Graph n) (hs : ∀ u v, G u v = G v u)
    (J : Subset n) (P : List (List (Fin n))) (hp : PathCover G P) :
    (P.flatMap (lowEdges J)).length ≤ (edgesOn G J).length := by
  have h : P.flatten.Nodup := hp.1.symm.nodup (nodupVerts n)
  apply length_subset _ _ (coverEdgesNodup J P h)
  intro e he
  obtain ⟨p,hm,hep⟩ := List.mem_flatMap.mp he
  exact lowEdgesSubset G hs J p (hp.2 p hm).2 (List.pairwise_flatten.mp h |>.1 p hm) _ hep

/-- The upper bound holds for every path cover, hence for the minimum one. -/
theorem bound448a {n} (G : Graph n) (hs : ∀ u v, G u v = G v u)
    (I : Subset n) (hi : TwoIndependent G I) (P : List (List (Fin n)))
    (hp : PathCover G P) :
    card I ≤ card (highHalf G) + (edgesOn G (lowHalf G)).length + P.length := by
  let H := highHalf G
  let L := lowHalf G
  let m := (edgesOn G L).length
  let h := card H
  let l := card L
  have hsum : h + l = n := by
    have h₀ := filter_split_length (verts n) H
    simpa [h, l, L, lowHalf, H, card, sum_bits, verts] using h₀.symm
  have hcount : l ≤ h + m + P.length := by
    have h₀ := cover_count L P
    have h₁ := (hp.1.filter L).length_eq
    have h₂ := (hp.1.filter (fun u => !L u)).length_eq
    rw [h₁,h₂] at h₀
    have h₃ := coverEdgeBound G hs L P hp
    have hl : (List.filter L (verts n)).length = l := by simp [l, card, sum_bits]
    have hh : (List.filter (fun u => !L u) (verts n)).length = h := by
      simp [h, card, sum_bits, L, lowHalf, H]
    rw [hl,hh] at h₀
    change (P.flatMap (lowEdges L)).length ≤ m at h₃
    omega
  change card I ≤ h + m + P.length
  by_cases he : ∃ u, I u = true ∧ H u = true
  · obtain ⟨u,hu,hH⟩ := he
    have hdeg : n/2 < degree G u := by simpa [H, highHalf] using hH
    have hin := hi u hu
    have hsplit := degreeSplit G I u
    have hmono : localCount G (fun u => !I u) u ≤ card (fun u => !I u) := by
      unfold localCount card
      apply sumMapMono
      intro v _
      cases hiv : I v <;> cases hg : G u v <;> simp [hiv,hg,bit]
    have hsI : card I + card (fun u => !I u) = n := by
      have h₀ := filter_split_length (verts n) I
      simpa [card,sum_bits,verts] using h₀.symm
    omega
  · have hI : card I ≤ l := by
      unfold l card
      apply sumMapMono
      intro u _
      cases hu : I u
      · simp [hu,bit]
      · have hh : H u = false := by
          cases hHu : H u
          · rfl
          · exact False.elim (he ⟨u,hu,hHu⟩)
        have hl : L u = true := by simp [L,lowHalf,← show H = highHalf G by rfl,hh]
        simp [hu,hl,bit]
    omega

def IsMinPathCover {n} (G : Graph n) (k : Nat) : Prop :=
  (∃ P, PathCover G P ∧ P.length = k) ∧
    ∀ P, PathCover G P → k ≤ P.length

theorem existsMinimumPathCover {n} (G : Graph n) :
    ∃ k, IsMinPathCover G k := by
  have hs : ∀ xs : List (Fin n), (xs.map (fun u => [u])).flatten = xs := by
    intro xs
    induction xs <;> simp_all
  let P : List (List (Fin n)) := (verts n).map (fun u => [u])
  have hp : PathCover G P := by
    refine ⟨?_,?_⟩
    · simp [P, hs]
    · intro q hq
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hq
      exact ⟨by simp, trivial⟩
  have aux (j : Nat) (hle : ∃ Q, PathCover G Q ∧ Q.length = j) :
      ∃ k, IsMinPathCover G k := by
    induction j using Nat.strongRecOn with
    | ind j ih =>
      by_cases h : ∃ Q, PathCover G Q ∧ Q.length < j
      · obtain ⟨Q,hQ,hl⟩ := h
        exact ih Q.length hl ⟨Q,hQ,rfl⟩
      · exact ⟨j,hle,fun Q hQ => Nat.le_of_not_gt (fun hl => h ⟨Q,hQ,hl⟩)⟩
  exact aux P.length ⟨P,hp,rfl⟩

/-- Exactly #448a, in a stronger form not requiring connectedness:
k is the minimum vertex-disjoint path-cover number, and the bound is
asserted for every 2-independent subset, equivalently for its maximum. -/
theorem conjecture448a {n} (G : Graph n) (symm : ∀ u v, G u v = G v u)
    (k : Nat) (hmin : IsMinPathCover G k) (I : Subset n) (hi : TwoIndependent G I) :
    card I ≤ card (highHalf G) + (edgesOn G (lowHalf G)).length + k := by
  obtain ⟨P,hP,hl⟩ := hmin.1
  simpa [hl] using bound448a G symm I hi P hP

#print axioms conjecture448a
#print axioms existsMinimumPathCover
#print axioms edgesOnExact
#print axioms edgesOnNodup
end Graffiti448a

namespace Graffiti448a
open Graffiti449

noncomputable def pathCoverNumber {n} (G : Graph n) : Nat :=
  Classical.choose (existsMinimumPathCover G)

theorem conjecture448a_exact {n} (G : Graph n) (hs : ∀ u v, G u v = G v u) :
    twoIndependenceNumber G ≤
      card (highHalf G) + (edgesOn G (lowHalf G)).length + pathCoverNumber G := by
  obtain ⟨I,hI,hcard⟩ := (Classical.choose_spec (maxNatExists (Attainable G) n (attainedEmpty G)
    (fun _ ⟨I, _, e⟩ => e ▸ cardLeOrder I))).1
  change card I = twoIndependenceNumber G at hcard
  rw [← hcard]
  exact conjecture448a G hs _ (Classical.choose_spec (existsMinimumPathCover G)) I hI

#print axioms conjecture448a_exact
end Graffiti448a
