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

set_option warningAsError true
namespace Graffiti450
open Graffiti449 Graffiti448a

def Leaf {n} (G : Graph n) : Subset n := fun u => decide (degree G u = 1)
def D2 {n} (G : Graph n) : Subset n := fun u => decide (degree G u = 2)
def PN {n} (G : Graph n) (J : Subset n) : Subset n := fun u => decide (localCount G J u = 1)
def support {n} (G : Graph n) : Subset n := fun u => decide (0 < localCount G (Leaf G) u)

def adjTo {n} (G : Graph n) (J : Subset n) : Subset n := fun u => decide (0 < localCount G J u)
def cap {n} (P Q : Subset n) : Subset n := fun u => P u && Q u
def comp {n} (P : Subset n) : Subset n := fun u => !P u

private theorem capIntro {n} {P Q : Subset n} {u} (p : P u = true) (q : Q u = true) :
    cap P Q u = true := by simp [cap,p,q]
private theorem capOut {n} {P Q : Subset n} {u} (h : cap P Q u = true) :
    P u = true ∧ Q u = true := by simpa [cap] using h
private theorem compIntro {n} {P : Subset n} {u} (p : P u = false) : comp P u = true := by
  simp [comp,p]
private theorem compOut {n} {P : Subset n} {u} (p : comp P u = true) : P u = false := by
  simpa [comp] using p

theorem cardMono {n} {P Q : Subset n} (h : ∀ u, P u = true → Q u = true) : card P ≤ card Q := by
  unfold card
  apply sumMapMono
  intro u _
  cases hp : P u
  · simp [hp, bit]
  · rw [h u hp]
    exact Nat.le_refl _

theorem localMono {n} (G : Graph n) {P Q : Subset n}
    (h : ∀ v, P v = true → Q v = true) (u : Fin n) :
    localCount G P u ≤ localCount G Q u := by
  unfold localCount
  apply cardMono
  intro v hv
  have hh := (Bool.and_eq_true _ _).mp hv
  simp [h v hh.1,hh.2]

theorem degreeUpper {n} (G : Graph n) (J : Subset n) (u : Fin n) :
    localCount G J u ≤ degree G u := by
  unfold localCount degree
  exact cardMono (fun _ e => ((Bool.and_eq_true _ _).mp e).2)

theorem localPos {n} (G : Graph n) (J : Subset n) (u : Fin n) :
    0 < localCount G J u ↔ ∃ v, G u v = true ∧ J v = true := by
  simp [localCount, card, sum_bits, List.length_filter_pos_iff, allVerts, and_comm]

theorem adjToExact {n} (G : Graph n) (J : Subset n) (u : Fin n) :
    adjTo G J u = true ↔ ∃ v, G u v = true ∧ J v = true := by
  simp only [adjTo, decide_eq_true_eq, localPos]

theorem cardTwo {n} (J : Subset n) {u v : Fin n} (hne : u ≠ v)
    (hu : J u = true) (hv : J v = true) : 2 ≤ card J := by
  have hmem (u : Fin n) (hu : J u = true) : u ∈ (verts n).filter J :=
    List.mem_filter.mpr ⟨allVerts u,hu⟩
  have a := hmem u hu
  have b := hmem v hv
  unfold card
  rw [sum_bits]
  generalize hz : List.filter J (verts n) = l at a b ⊢
  match l with
  | [] => simp at a
  | [x] =>
    simp only [List.mem_singleton] at a b
    exact False.elim (hne (a.trans b.symm))
  | x::y::xs => simp

theorem localTwo {n} (G : Graph n) (J : Subset n) (w : Fin n) {u v : Fin n}
    (hne : u ≠ v) (hu : J u = true) (hv : J v = true)
    (hwu : G w u = true) (hwv : G w v = true) :
    2 ≤ localCount G J w := by
  apply cardTwo _ hne
  · simp [hu,hwu]
  · simp [hv,hwv]

theorem localUnique {n} (G : Graph n) (I : Subset n) {w u v : Fin n}
    (h : localCount G I w ≤ 1) (hu : I u = true) (hv : I v = true)
    (hwu : G w u = true) (hwv : G w v = true) : u = v := by
  by_cases e : u = v
  · exact e
  · have z := localTwo G I w e hu hv hwu hwv
    omega

theorem localNew {n} (G : Graph n) (I : Subset n) {w u : Fin n}
    (h : 2 ≤ localCount G I w) :
    ∃ v, v ≠ u ∧ G w v = true ∧ I v = true := by
  classical
  by_cases hn : ∃ v, v ≠ u ∧ G w v = true ∧ I v = true
  · exact hn
  apply False.elim
  unfold localCount card at h
  rw [sum_bits] at h
  generalize eq : (verts n).filter (fun v => I v && G w v) = l at h
  have hnd : l.Nodup := by rw [← eq]; exact List.Pairwise.filter _ (nodupVerts n)
  have hh : ∀ v ∈ l, v = u := by
    rw [← eq]
    intro v hv
    have he := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hv).2
    by_cases hne : v = u
    · exact hne
    · exact False.elim (hn ⟨v,hne,he.2,he.1⟩)
  cases l with
  | nil => simp at h
  | cons a ls =>
    cases ls with
    | nil => simp at h
    | cons b ls =>
      have eb := hh b (by simp)
      have ea := hh a (by simp)
      exact (List.nodup_cons.mp hnd).1 (by simp [ea,eb])

theorem localOfPoint {n} (G : Graph n) (P Q : Subset n) (u : Fin n)
    (h : ∀ v, G u v = true → P v = true → Q v = true) :
    localCount G P u ≤ localCount G Q u := by
  unfold localCount
  apply cardMono
  intro v hv
  have hh := (Bool.and_eq_true _ _).mp hv
  simp [h v hh.2 hh.1,hh.2]

theorem rowsLower {n} (G : Graph n) (P Q : Subset n) (k : Nat)
    (h : ∀ u, P u = true → k ≤ localCount G Q u) : k*card P ≤ pairCount G P Q := by
  rw [pairRows]
  unfold card
  have aux : ∀ l : List (Fin n), k*sumMap l (fun u => bit (P u)) =
      sumMap l (fun u => if P u then k else 0) := by
    intro l
    induction l with
    | nil => simp [sumMap]
    | cons u l ih =>
      cases hu : P u <;> simp [sumMap, hu, bit, Nat.mul_add] at * <;> omega
  rw [aux]
  apply sumMapMono
  intro u _
  cases he : P u
  · simp [he]
  · simpa [he] using h u he

theorem rowsUpper {n} (G : Graph n) (P Q : Subset n) (k : Nat)
    (h : ∀ u, P u = true → localCount G Q u ≤ k) : pairCount G P Q ≤ k*card P := by
  rw [pairRows]
  unfold card
  have aux : ∀ l : List (Fin n), k*sumMap l (fun u => bit (P u)) =
      sumMap l (fun u => if P u then k else 0) := by
    intro l
    induction l with
    | nil => simp [sumMap]
    | cons u l ih =>
      cases hu : P u <;> simp [sumMap, hu, bit, Nat.mul_add] at * <;> omega
  rw [aux]
  apply sumMapMono
  intro u _
  cases he : P u
  · simp [he]
  · simpa [he] using h u he

inductive Walk {n} (G : Graph n) : Fin n → Fin n → Prop
  | stop (u : Fin n) : Walk G u u
  | step {u v w : Fin n} : G u v = true → Walk G v w → Walk G u w

def Connected {n} (G : Graph n) : Prop := ∀ u v, Walk G u v

theorem noAdjacentLeaves {n} (G : Graph n) (hn : 3 < n)
    (hs : ∀ u v, G u v = G v u) (hc : Connected G)
    {u v : Fin n} (hu : Leaf G u = true) (hv : Leaf G v = true) (huv : G u v = true) :
    False := by
  have du : degree G u ≤ 1 := by simp [Leaf] at hu; omega
  have dv : degree G v ≤ 1 := by simp [Leaf] at hv; omega
  have hstep (x y : Fin n) (hx : x = u ∨ x = v) (hxy : G x y = true) :
      y = u ∨ y = v := by
    rcases hx with eq | eq
    · subst x
      right
      exact localUnique G (fun _ => true) (by simpa [localCount,degree] using du)
        rfl rfl hxy huv
    · subst x
      left
      exact localUnique G (fun _ => true) (by simpa [localCount,degree] using dv)
        rfl rfl hxy ((hs v u).trans huv)
  have hwalk (x y : Fin n) (p : Walk G x y) (hh : x = u ∨ x = v) :
      y = u ∨ y = v := by
    induction p with
    | stop => exact hh
    | step h _ ih => exact ih (hstep _ _ hh h)
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have ha := hwalk u a (hc u a) (Or.inl rfl)
  have hb := hwalk u b (hc u b) (Or.inl rfl)
  have hc' := hwalk u c (hc u c) (Or.inl rfl)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc' with hc' | hc' <;>
    replace ha := congrArg Fin.val ha <;> replace hb := congrArg Fin.val hb <;>
    replace hc' := congrArg Fin.val hc' <;> dsimp [a,b,c] at ha hb hc' <;> omega

theorem leafNotSupport {n} (G : Graph n) (hn : 3 < n)
    (hs : ∀ u v, G u v = G v u) (hc : Connected G)
    {u : Fin n} (hu : Leaf G u = true) : support G u = false := by
  cases he : support G u
  · rfl
  · change adjTo G (Leaf G) u = true at he
    obtain ⟨v,ge,hv⟩ := (adjToExact G (Leaf G) u).mp he
    exact False.elim (noAdjacentLeaves G hn hs hc hu hv ge)

theorem degreePos {n} (G : Graph n) {u v : Fin n} (h : G u v = true) : 0 < degree G u := by
  have he := (localPos G (fun _ => true) u).mpr ⟨v,h,rfl⟩
  simpa [localCount,degree] using he

/-- #450 for all selected sets, not only a maximum one. -/
theorem bound450 {n} (G : Graph n) (hn : 3 < n)
    (hs : ∀ u v, G u v = G v u) (hc : Connected G)
    (I : Subset n) (hi : TwoIndependent G I) :
    card I ≤ card (comp (support G)) + card (PN G (D2 G)) + card (PN G (low G)) := by
  let S := support G
  let K := D2 G
  let A := cap (Leaf G) (comp I)
  let B := cap (cap K (comp I)) (comp S)
  let C := cap (cap K (comp I)) S
  let T := cap (PN G K) (comp S)
  let I_S := cap I S
  let U := cap (comp S) (comp I)
  let R := cap (cap I_S (comp (PN G K))) (comp (PN G (low G)))
  let R₀ := cap R (adjTo G A)
  let R₁ := cap R (comp (adjTo G A))

  have leafnS (v : Fin n) (h : Leaf G v = true) : S v = false :=
    leafNotSupport G hn hs hc h
  have diamA (u : Fin n) (h : A u = true) : degree G u = 1 := by
    simpa [Leaf] using (capOut h).1
  have diamK (u : Fin n) (h : K u = true) : degree G u = 2 := by
    simpa [K,D2] using h

  have aLower : card R₀ ≤ pairCount G R₀ A := by
    have h := rowsLower G R₀ A 1 (fun u hu => by
      have hpos := (adjToExact G A u).mp (capOut hu).2
      exact (localPos G A u).mpr hpos)
    simpa using h
  have aUpper : pairCount G R₀ A ≤ card A := by
    rw [pairSwap G hs R₀ A]
    have h := rowsUpper G A R₀ 1 (fun u hu => (diamA u hu) ▸ degreeUpper G R₀ u)
    simpa using h
  have boundA : card R₀ ≤ card A := Nat.le_trans aLower aUpper

  have r1Rules (u : Fin n) (h : R₁ u = true) :
      2 ≤ localCount G (cap K (comp I)) u := by
    have hr := capOut h
    have hrr := capOut hr.1
    have hrrr := capOut hrr.1
    have hselected := capOut hrrr.1
    have huI := hselected.1
    have noA := compOut hr.2
    have no2 := compOut hrrr.2
    have noLow := compOut hrr.2
    have hsupport : adjTo G (Leaf G) u = true := hselected.2
    obtain ⟨l, hul, hlL⟩ := (adjToExact G (Leaf G) u).mp hsupport
    have chooseL : I l = true := by
      cases he : I l
      · have ha : A l = true := capIntro hlL (compIntro he)
        have bad := (adjToExact G A u).mpr ⟨l,hul,ha⟩
        rw [noA] at bad
        contradiction
      · rfl
    have hlDegree : degree G l = 1 := by simpa [Leaf] using hlL
    have hlLow : low G l = true := by simp [low,high,hlDegree]
    have lowPos := (localPos G (low G) u).mpr ⟨l,hul,hlLow⟩
    have lowNe : localCount G (low G) u ≠ 1 := by simpa [PN] using noLow
    have hlc : 2 ≤ localCount G (low G) u := by omega
    obtain ⟨v,vne,huv,hlv⟩ := localNew G (low G) hlc (u := l)
    have forbidden (w : Fin n) (hwne : w ≠ l) (huw : G u w = true) :
        I w = false := by
      cases he : I w
      · rfl
      · exact False.elim (hwne (localUnique G I (hi u huI) he chooseL huw hul))
    have hvI : I v = false := forbidden v vne huv
    have hvpos := degreePos G ((hs v u).trans huv)
    have hvNotLeaf : degree G v ≠ 1 := by
      intro he
      have hl : Leaf G v = true := by simp [Leaf, he]
      have A_v : A v = true := capIntro hl (compIntro hvI)
      have ha := (adjToExact G A u).mpr ⟨v,huv,A_v⟩
      rw [noA] at ha
      contradiction
    have hvLow : ¬ 3 ≤ degree G v := by simpa [low,high] using hlv
    have hvK : K v = true := by
      have hvd : degree G v = 2 := by omega
      simp [K,D2,hvd]
    have KPos := (localPos G K u).mpr ⟨v,huv,hvK⟩
    have KNe : localCount G K u ≠ 1 := by simpa [PN] using no2
    have hKm : localCount G K u ≤ localCount G (cap K (comp I)) u := by
      apply localOfPoint
      intro w huw hwK
      have hne : w ≠ l := by
        intro e
        subst w
        have bad := diamK l hwK
        omega
      exact capIntro hwK (compIntro (forbidden w hne huw))
    omega

  have r1Lower : 2*card R₁ ≤ pairCount G R₁ (cap K (comp I)) :=
    rowsLower G R₁ _ 2 r1Rules

  have r1Split : pairCount G R₁ (cap K (comp I)) = pairCount G R₁ C + pairCount G R₁ B := by
    have h := pairSplit G R₁ (cap K (comp I)) S
    exact h

  have bUpper : pairCount G R₁ B ≤ 2*card B := by
    rw [pairSwap G hs R₁ B]
    apply rowsUpper
    intro u hu
    have hv := diamK u (capOut (capOut hu).1).1
    exact hv ▸ degreeUpper G R₁ u

  have cUpper : pairCount G R₁ C ≤ card C := by
    rw [pairSwap G hs R₁ C]
    suffices he : ∀ u, C u = true → localCount G R₁ u ≤ 1 by
      simpa using rowsUpper G C R₁ 1 he
    intro u hu
    have deg := diamK u (capOut (capOut hu).1).1
    have s : adjTo G (Leaf G) u = true := (capOut hu).2
    obtain ⟨v,uv,vL⟩ := (adjToExact G (Leaf G) u).mp s
    have hleaf := (localPos G (Leaf G) u).mpr ⟨v,uv,vL⟩
    have hmono : localCount G R₁ u ≤ localCount G (comp (Leaf G)) u := by
      apply localMono
      intro w hw
      have hs : S w = true := (capOut (capOut (capOut (capOut hw).1).1).1).2
      cases he : Leaf G w
      · exact compIntro he
      · have bad := leafnS w he
        rw [bad] at hs
        contradiction
    have hsplit := degreeSplit G (Leaf G) u
    change degree G u = localCount G (Leaf G) u + localCount G (comp (Leaf G)) u at hsplit
    omega

  have cLowerT : card C ≤ pairCount G C T := by
    suffices h : ∀ u, C u = true → 1 ≤ localCount G T u by
      simpa using rowsLower G C T 1 h
    intro u hu
    have Ku : K u = true := (capOut (capOut hu).1).1
    have s : adjTo G (Leaf G) u = true := (capOut hu).2
    obtain ⟨v,uv,vL⟩ := (adjToExact G (Leaf G) u).mp s
    have dve : degree G v = 1 := by simpa [Leaf] using vL
    have up := degreeUpper G K v
    have lo := (localPos G K v).mpr ⟨u,(hs v u).trans uv,Ku⟩
    have one : localCount G K v = 1 := by omega
    have pv : PN G K v = true := by simp [PN, one]
    have tv : T v = true := capIntro pv (compIntro (leafnS v vL))
    exact (localPos G T u).mpr ⟨v,uv,tv⟩

  have cUpperT : pairCount G C T ≤ card T := by
    rw [pairSwap G hs C T]
    suffices he : ∀ u, T u = true → localCount G C u ≤ 1 by
      simpa using rowsUpper G T C 1 he
    intro u hu
    have p : PN G K u = true := (capOut hu).1
    have one : localCount G K u = 1 := by simpa [PN] using p
    have hmono : localCount G C u ≤ localCount G K u :=
      localMono G (fun _ h => (capOut (capOut h).1).1) u
    omega

  have hcap : card R₁ ≤ card B + card T := by omega

  have au : card A ≤ card (cap U (Leaf G)) := by
    apply cardMono
    intro u hu
    have hu' := capOut hu
    exact capIntro (capIntro (compIntro (leafnS u hu'.1)) hu'.2) hu'.1
  have bu : card B ≤ card (cap U (comp (Leaf G))) := by
    apply cardMono
    intro u hu
    have hu' := capOut hu
    have hki := capOut hu'.1
    have hK := diamK u hki.1
    have nLeaf : Leaf G u = false := by simp [Leaf,hK]
    exact capIntro (capIntro hu'.2 hki.2) (compIntro nLeaf)
  have huSplit : card U = card (cap U (Leaf G)) + card (cap U (comp (Leaf G))) :=
    cardSplit U (Leaf G)
  have hRsplit : card R = card R₀ + card R₁ := cardSplit R (adjTo G A)
  have hR : card R ≤ card U + card T := by omega

  have pc1 : card (cap I_S (PN G K)) ≤ card (cap (PN G K) S) := by
    apply cardMono
    intro u hu
    exact capIntro (capOut hu).2 (capOut (capOut hu).1).2
  have pc2 : card (cap (cap I_S (comp (PN G K))) (PN G (low G))) ≤ card (PN G (low G)) := by
    exact cardMono (fun _ h => (capOut h).2)
  have hIS1 : card I_S = card (cap I_S (PN G K)) + card (cap I_S (comp (PN G K))) :=
    cardSplit I_S (PN G K)
  have hIS2 : card (cap I_S (comp (PN G K))) =
      card (cap (cap I_S (comp (PN G K))) (PN G (low G))) + card R :=
    cardSplit (cap I_S (comp (PN G K))) (PN G (low G))
  have hPT : card (PN G K) = card (cap (PN G K) S) + card T := cardSplit (PN G K) S
  have hIT : card I = card I_S + card (cap I (comp S)) := cardSplit I S
  have hYU : card (comp S) = card (cap I (comp S)) + card U := by
    have he := cardSplit (comp S) I
    change card (comp S) = card (cap (comp S) I) + card U at he
    have heq : cap (comp S) I = cap I (comp S) := by
      funext u
      exact Bool.and_comm _ _
    rwa [heq] at he
  change card I ≤ card (comp S) + card (PN G K) + card (PN G (low G))
  omega

theorem conjecture450 {n} (G : Graph n) (hn : 3 < n)
    (hs : ∀ u v, G u v = G v u) (hc : Connected G) :
    twoIndependenceNumber G ≤
      card (comp (support G)) + card (PN G (D2 G)) + card (PN G (low G)) := by
  obtain ⟨I, hi, he⟩ := (Classical.choose_spec (maxNatExists (Attainable G) n (attainedEmpty G)
    (fun _ ⟨I, _, e⟩ => e ▸ cardLeOrder I))).1
  change card I = twoIndependenceNumber G at he
  rw [← he]
  exact bound450 G hn hs hc I hi

#print axioms conjecture450
end Graffiti450
