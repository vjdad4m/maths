import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.List.Nodup

namespace Graffiti199K2

open SimpleGraph Finset
open scoped Sym2

lemma tree_of_rank {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : V) (rank : V → ℕ)
    (hne : ∀ ⦃x y⦄, G.Adj x y → rank x ≠ rank y)
    (hr : ∀ ⦃x⦄, ¬(G.Adj r x ∧ rank x < rank r))
    (hp : ∀ x, x ≠ r → ∃! y, G.Adj x y ∧ rank y < rank x) :
    G.IsTree := by
  classical
  let p : {x // x ≠ r} → V := fun x => Classical.choose (ExistsUnique.exists (hp x x.prop))
  have pp (x : {x // x ≠ r}) : G.Adj x (p x) ∧ rank (p x) < rank x :=
    Classical.choose_spec (ExistsUnique.exists (hp x x.prop))
  have pu (x : {x // x ≠ r}) {y : V} (hy : G.Adj x y ∧ rank y < rank x) : y = p x :=
    (hp x x.prop).unique hy (pp x)
  have reach (x : V) : G.Reachable r x := by
    induction h : rank x using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hx : x = r
      · subst x; exact SimpleGraph.Reachable.rfl
      · exact (ih _ (by rw [← h]; exact (pp ⟨x,hx⟩).2) _ rfl).trans (pp ⟨x,hx⟩).1.symm.reachable
  haveI : Nonempty V := ⟨r⟩
  have hcon : G.Connected := ⟨fun x y => (reach x).symm.trans (reach y)⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hcon, ?_⟩
  let f : {x // x ≠ r} → G.edgeSet :=
    fun x => ⟨s((x : V), p x), (G.mem_edgeSet).mpr (pp x).1⟩
  have hfi : Function.Injective f := by
    intro a b h
    have hab : s((a : V), p a) = s((b : V), p b) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hab with hsame | hrev
    · exact Subtype.ext hsame.1
    · have ha := (pp a).2
      have hb := (pp b).2
      rw [hrev.2, hrev.1] at ha
      omega
  have hfs : Function.Surjective f := by
    rintro ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro a b he
    have had : G.Adj a b := (G.mem_edgeSet).mp he
    rcases lt_or_gt_of_ne (hne had) with hab | hab
    · have hbr : b ≠ r := by intro h; subst b; exact hr ⟨had.symm,hab⟩
      refine ⟨⟨b,hbr⟩, Subtype.ext ?_⟩
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,(pu ⟨b,hbr⟩ ⟨had.symm,hab⟩).symm⟩)
    · have har : a ≠ r := by intro h; subst a; exact hr ⟨had,hab⟩
      refine ⟨⟨a,har⟩, Subtype.ext ?_⟩
      exact Sym2.eq_iff.mpr (Or.inl ⟨rfl,(pu ⟨a,har⟩ ⟨had,hab⟩).symm⟩)
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfi,hfs⟩)]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x => x = r)]
  have hr1 : Fintype.card {x // x = r} = 1 := Fintype.card_unique
  have hv1 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  omega


/-- The conventional finite statement "vertex connectivity at least k".
The order guard gives complete graphs their usual connectivity n-1. -/
def ConnectivityAtLeast {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected

theorem min_degree_of_connectivityAtLeast {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : ConnectivityAtLeast G k) (v : V) :
    k ≤ (G.neighborFinset v).card := by
  by_contra! hd
  let S := G.neighborFinset v
  have hv : v ∉ S := by simp [S]
  have hlt : (insert v S).card < Fintype.card V := by
    rw [Finset.card_insert_of_not_mem hv]
    have hk' := hk.1
    change S.card < k at hd
    omega
  obtain ⟨w,hw⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show (insert v S).card < (Finset.univ : Finset V).card by simpa using hlt)
  have hw' := hw.2
  rw [Finset.mem_insert] at hw'
  have hwd : w ≠ v := fun h => hw' (Or.inl h)
  let W : Set V := (↑S : Set V)ᶜ
  let a : W := ⟨v,hv⟩
  let b : W := ⟨w,fun h => hw' (Or.inr h)⟩
  let H := G.induce W
  have hn (x : W) : ¬H.Adj a x :=
    fun h => x.prop ((G.mem_neighborFinset _ _).mpr h)
  have hr {x : W} (p : H.Walk a x) : x = a := by
    cases p with
    | nil => rfl
    | cons h _ => exact (hn _ h).elim
  have hcon : H.Connected := hk.2 S hd
  obtain ⟨p⟩ := hcon.preconnected a b
  exact hwd (congrArg (fun x : W => (x : V)) (hr p))

noncomputable def vertexConnectivity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.range (Fintype.card V)).filter (ConnectivityAtLeast G)).sup id

theorem connectivityAtLeast_vertexConnectivity {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : ConnectivityAtLeast G (vertexConnectivity G) := by
  classical
  let A := (Finset.range (Fintype.card V)).filter (ConnectivityAtLeast G)
  have h0 : ConnectivityAtLeast G 0 := ⟨Fintype.card_pos, by simp⟩
  have hA : A.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h0.1, h0⟩⟩
  obtain ⟨k,hk,hk'⟩ := Finset.exists_mem_eq_sup A hA id
  change ConnectivityAtLeast G (A.sup id)
  rw [hk']
  exact (Finset.mem_filter.mp hk).2

theorem vertexConnectivity_pos {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hc : G.Connected) (hn : 1 < Fintype.card V) :
    0 < vertexConnectivity G := by
  classical
  change 1 ≤ vertexConnectivity G
  unfold vertexConnectivity
  apply Finset.le_sup (f := id)
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn,hn,?_⟩
  intro S hS
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
  subst S
  let W : Set V := ((↑(∅ : Finset V) : Set V)ᶜ)
  let φ : G →g G.induce W :=
    ⟨fun v => ⟨v, by simp [W]⟩, fun h => h⟩
  have hsur : Function.Surjective φ := by
    intro v
    exact ⟨v, Subtype.ext rfl⟩
  exact hc.map φ hsur

/-- The maximum number of vertices in an induced tree. -/
noncomputable def treeNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter
    (fun S : Finset V => (G.induce (↑S : Set V)).IsTree)).sup Finset.card

theorem card_le_treeNumber {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Finset V) (hS : (G.induce (↑S : Set V)).IsTree) : S.card ≤ treeNumber G := by
  classical
  unfold treeNumber
  apply Finset.le_sup (b := S)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS⟩




/-- The three unlabeled trees of order five, in increasing parent order. -/
private def shapeAdj (shape : Fin 3) (i j : Fin 5) : Bool :=
  let a := min i.val j.val
  let b := max i.val j.val
  if shape.val = 0 then decide (a+1=b)
  else if shape.val = 1 then
    decide ((a=0 ∧ (b=1 ∨ b=2 ∨ b=3)) ∨ (a=1 ∧ b=4))
  else decide (a=0 ∧ 0<b)

private def ShapeEmbedding {V : Type*} (G : SimpleGraph V) (s : Fin 3) (f : Fin 5 ↪ V) : Prop :=
  ∀ i j, G.Adj (f i) (f j) ↔ shapeAdj s i j = true

def NoTree5 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ s : Fin 3, ∀ f : Fin 5 ↪ V, ¬ ShapeEmbedding G s f

private theorem rankShape (s : Fin 3) :
    ∀ i : Fin 5, i ≠ 0 →
      ∃ j : Fin 5, shapeAdj s i j = true ∧ j.val < i.val ∧
        ∀ k : Fin 5, shapeAdj s i k = true → k.val < i.val → k = j := by
  decide +revert

private theorem shape_ne (s : Fin 3) : ∀ i j : Fin 5, shapeAdj s i j = true → i ≠ j := by
  decide +revert

private theorem embedding_induces_tree {V : Type*} {G : SimpleGraph V}
    (s : Fin 3) (f : Fin 5 ↪ V) (h : ShapeEmbedding G s f) :
    ∃ S : Finset V, S.card = 5 ∧ (G.induce (↑S : Set V)).IsTree := by
  classical
  let S := univ.map f
  let F (i : Fin 5) : (↑S : Set V) := ⟨f i, mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩
  have hInj : Function.Injective F := fun _ _ e => f.injective (congrArg Subtype.val e)
  have hSurj : Function.Surjective F := by
    intro v
    obtain ⟨i,_,hi⟩ := mem_map.mp v.property
    exact ⟨i,Subtype.ext hi⟩
  let E := Equiv.ofBijective F ⟨hInj,hSurj⟩
  let H := G.induce (↑S : Set V)
  let rank (v : (↑S : Set V)) : ℕ := (E.symm v).val
  have hF (i : Fin 5) : rank (F i) = i.val :=
    congrArg Fin.val (E.symm_apply_apply i)
  have hAdj (i j : Fin 5) : H.Adj (F i) (F j) ↔ shapeAdj s i j = true := h i j
  refine ⟨S,by simp [S],?_⟩
  apply tree_of_rank (F 0) rank
  · intro x y he
    obtain ⟨i,rfl⟩ := hSurj x
    obtain ⟨j,rfl⟩ := hSurj y
    rw [hF,hF]
    exact fun h' => shape_ne s i j ((hAdj i j).mp he) (Fin.ext h')
  · intro x hx
    rw [hF] at hx
    exact Nat.not_lt_zero _ hx.2
  · intro x hx
    obtain ⟨i,rfl⟩ := hSurj x
    have hi : i ≠ 0 := fun he => hx (congrArg F he)
    obtain ⟨j,hj,hlt,hu⟩ := rankShape s i hi
    refine ⟨F j,⟨(hAdj i j).mpr hj,by rwa [hF,hF]⟩,?_⟩
    rintro y ⟨hy,hy2⟩
    obtain ⟨k,rfl⟩ := hSurj y
    rw [hF,hF] at hy2
    exact congrArg F (hu k ((hAdj i k).mp hy) hy2)

theorem noTree5_of_treeNumber_le_four {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h : treeNumber G ≤ 4) : NoTree5 G := by
  intro s f he
  obtain ⟨S,hs,hS⟩ := embedding_induces_tree s f he
  have hcard := card_le_treeNumber S hS
  omega

private def clawAdj (i j : Fin 4) : Bool :=
  decide ((i.val = 0 ∧ 0 < j.val) ∨ (j.val = 0 ∧ 0 < i.val))

def IsClaw {V : Type*} (G : SimpleGraph V) (Q : Fin 4 ↪ V) : Prop :=
  ∀ i j, G.Adj (Q i) (Q j) ↔ clawAdj i j = true

def Outside {V : Type*} (Q : Fin 4 ↪ V) (x : V) : Prop := ∀ i, x ≠ Q i

abbrev Mask := Fin 16

def HasMask {V : Type*} (G : SimpleGraph V) (Q : Fin 4 ↪ V) (x : V) (m : Mask) : Prop :=
  ∀ i, G.Adj (Q i) x ↔ m.val.testBit i.val = true

theorem mask_exists {V : Type*} (G : SimpleGraph V) (Q : Fin 4 ↪ V) (x : V) :
    ∃ m : Mask, HasMask G Q x m := by
  classical
  have h : ∀ f : Fin 4 → Bool, ∃ m : Mask, ∀ i : Fin 4, m.val.testBit i.val = f i := by decide
  obtain ⟨m,hm⟩ := h (fun i => decide (G.Adj (Q i) x))
  exact ⟨m,fun i => by rw [hm i,decide_eq_true_eq]⟩

def Near {V : Type*} (G : SimpleGraph V) (Q : Fin 4 ↪ V) (x : V) : Prop :=
  Outside Q x ∧ ∃ i, G.Adj (Q i) x

def Far {V : Type*} (G : SimpleGraph V) (Q : Fin 4 ↪ V) (x : V) : Prop :=
  Outside Q x ∧ HasMask G Q x 0

private def packed {V : Type*} {n : ℕ} (Q : Fin 4 ↪ V) (f : Fin n ↪ V)
    (hd : ∀ i, Outside Q (f i)) : Fin (4+n) ↪ V where
  toFun := Fin.addCases Q f
  inj' := by
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [Fin.addCases_left,Fin.castAdd_inj]; exact fun h => Q.injective h
    · simp only [Fin.addCases_left,Fin.addCases_right]
      intro h; exact (hd _ _ h.symm).elim
    · simp only [Fin.addCases_left,Fin.addCases_right]
      intro h; exact (hd _ _ h).elim
    · simp only [Fin.addCases_right]
      intro h; exact congrArg (Fin.natAdd 4) (f.injective h)

private theorem packed_apply {V : Type*} {n : ℕ} (Q : Fin 4 ↪ V) (f : Fin n ↪ V)
    (hd : ∀ i, Outside Q (f i)) (i : Fin (4+n)) :
    packed Q f hd i = Fin.addCases Q f i := rfl

private def packedAdj {n : ℕ} (m : Fin n → Mask) (E : Fin n → Fin n → Bool) :
    Fin (4+n) → Fin (4+n) → Bool := fun i j =>
  if hi : i.val < 4 then
    if hj : j.val < 4 then clawAdj ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else (m ⟨j.val-4,by have := j.isLt; omega⟩).val.testBit i.val
  else
    if hj : j.val < 4 then (m ⟨i.val-4,by have := i.isLt; omega⟩).val.testBit j.val
    else E ⟨i.val-4,by have := i.isLt; omega⟩ ⟨j.val-4,by have := j.isLt; omega⟩

private theorem packed_agree {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (hQ : IsClaw G Q) {n : ℕ} (f : Fin n ↪ V) (hd : ∀ i, Outside Q (f i))
    (m : Fin n → Mask) (hm : ∀ i, HasMask G Q (f i) (m i)) (E : Fin n → Fin n → Bool)
    (hE : ∀ i j, G.Adj (f i) (f j) ↔ E i j = true) :
    ∀ i j, G.Adj (packed Q f hd i) (packed Q f hd j) ↔ packedAdj m E i j = true := by
  have pos (i : Fin 4) : i.val < 4 := i.isLt
  have neg (i : Fin n) : ¬ 4+i.val < 4 := by omega
  have sub (i : Fin n) : 4+i.val-4 = i.val := by omega
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · simpa only [packed_apply, packedAdj, Fin.addCases_left,
      Fin.coe_castAdd, dif_pos (pos _)] using hQ _ _
  · simpa only [packed_apply, packedAdj, Fin.addCases_left,
      Fin.addCases_right, Fin.coe_castAdd, Fin.coe_natAdd,dif_pos (pos _),dif_neg (neg _),sub]
      using hm _ _
  · simpa only [packed_apply, packedAdj, Fin.addCases_left,
      Fin.addCases_right, Fin.coe_castAdd, Fin.coe_natAdd,dif_pos (pos _),dif_neg (neg _),sub,
      G.adj_comm] using hm _ _
  · simpa only [packed_apply, packedAdj, Fin.addCases_right,
      Fin.coe_natAdd,dif_neg (neg _),sub] using hE _ _

private abbrev CW (n : ℕ) := Fin 3 × (Fin 5 → Fin n)

private def witnessOK {n : ℕ} (A : Fin n → Fin n → Bool) (w : CW n) : Prop :=
  (∀ i j, w.2 i = w.2 j → i = j) ∧
    ∀ i j, A (w.2 i) (w.2 j) = shapeAdj w.1 i j

private instance {n : ℕ} (A : Fin n → Fin n → Bool) (w : CW n) :
    Decidable (witnessOK A w) := by
  unfold witnessOK
  infer_instance

private def optionOK {n : ℕ} (A : Fin n → Fin n → Bool) : Option (CW n) → Prop
  | none => True
  | some w => witnessOK A w

private instance {n : ℕ} (A : Fin n → Fin n → Bool) (w : Option (CW n)) :
    Decidable (optionOK A w) := by cases w <;> unfold optionOK <;> infer_instance

private theorem witness_avoided {V : Type*} {G : SimpleGraph V} (h : NoTree5 G)
    {n : ℕ} (F : Fin n ↪ V) (A : Fin n → Fin n → Bool)
    (ha : ∀ i j, G.Adj (F i) (F j) ↔ A i j = true)
    (w : Option (CW n)) (hw : optionOK A w) : w.isNone = true := by
  cases w with
  | none => rfl
  | some t =>
    obtain ⟨hi,hr⟩ := hw
    exfalso
    apply h t.1 ⟨fun i => F (t.2 i),fun i j e => hi i j (F.injective e)⟩
    intro i j
    change G.Adj (F (t.2 i)) (F (t.2 j)) ↔ shapeAdj t.1 i j = true
    rw [ha,hr]

private def edge2 (e : Bool) (i j : Fin 2) : Bool := if i = j then false else e

private def edge3 (a b c : Bool) (i j : Fin 3) : Bool :=
  let l := min i.val j.val
  let h := max i.val j.val
  if i = j then false else if l = 0 then if h = 1 then a else b else c

private def edge4 (e : Bool) (i j : Fin 4) : Bool :=
  let l := min i.val j.val
  let h := max i.val j.val
  if i = j then false else
    if l = 0 ∧ h = 1 then e else decide ((l=0 ∧ h=2) ∨ (l=1 ∧ h=3))

private def oneCode (a : Mask) := packedAdj ![a] (fun _ _ => false)
private def pairCode (a b : Mask) (e : Bool) := packedAdj ![a,b] (edge2 e)
private def attachCode (a b : Mask) (e same : Bool) := packedAdj ![a,b,0] (edge3 e true same)
private def farCode (a : Mask) (share : Bool) := packedAdj ![a,0,0] (edge3 true share (!share))
private def crossCode (a b : Mask) (e : Bool) := packedAdj ![a,b,0,0] (edge4 e)
private def oneTable : List (Option (CW 5)) := [none,some (2,![0,1,2,3,4]),some (1,![0,1,2,3,4]),none,some (1,![0,2,1,3,4]),none,none,none,some (1,![0,3,1,2,4]),none,none,none,none,none,none,none]

private def oneWitness (a : Mask) : Option (CW 5) :=
  (oneTable[a.val]?).getD none

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem oneValid : ∀ a : Mask, optionOK (oneCode a) (oneWitness a) := by
  decide

private def pairRow0 : List (Option (CW 6)) := [
  none,none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,some (1,![0,5,2,3,4]),some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,some (1,![0,5,1,3,4]),
  none,some (0,![3,0,1,5,4]),none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,some (1,![0,5,1,2,4]),none,some (0,![2,0,1,5,4]),none,none,
  none,some (0,![1,0,2,5,4]),none,none,none,some (2,![5,1,2,3,4]),
  none,some (2,![5,1,2,3,4])]
private def pairRow1 : List (Option (CW 6)) := [
  some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),
  some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),
  some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),
  some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),
  some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4]),
  some (2,![0,1,2,3,4]),some (2,![0,1,2,3,4])]
private def pairRow2 : List (Option (CW 6)) := [
  some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),
  some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),
  some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),
  some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),
  some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4]),
  some (1,![0,1,2,3,4]),some (1,![0,1,2,3,4])]
private def pairRow3 : List (Option (CW 6)) := [
  none,some (1,![0,4,2,3,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (2,![0,2,3,4,5]),none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,none,
  some (1,![0,2,3,4,5]),none,none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,none,some (1,![0,3,2,4,5]),none,none,none,
  none,some (1,![5,4,2,3,1]),none,some (1,![5,4,2,3,1]),some (1,![5,1,2,3,4]),none,
  some (1,![5,1,2,3,4]),none]
private def pairRow4 : List (Option (CW 6)) := [
  some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),
  some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),
  some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),
  some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),
  some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4]),
  some (1,![0,2,1,3,4]),some (1,![0,2,1,3,4])]
private def pairRow5 : List (Option (CW 6)) := [
  none,some (1,![0,4,1,3,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (2,![0,1,3,4,5]),none,
  some (1,![0,1,3,4,5]),none,none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,none,none,some (1,![5,4,1,3,2]),none,some (1,![5,4,1,3,2]),
  some (1,![0,3,1,4,5]),none,none,none,some (1,![5,2,1,3,4]),none,
  some (1,![5,2,1,3,4]),none]
private def pairRow6 : List (Option (CW 6)) := [
  none,some (0,![3,0,1,4,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (1,![0,2,3,5,4]),none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (1,![0,1,3,5,4]),none,
  some (1,![1,0,4,5,3]),none,none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,some (1,![4,5,1,2,3]),some (0,![4,2,0,3,5]),none,some (0,![2,4,1,5,3]),none,
  some (0,![4,1,0,3,5]),none,some (0,![1,4,2,5,3]),none,none,none,
  none,none]
private def pairRow7 : List (Option (CW 6)) := [
  none,none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,none,
  none,none,none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,some (1,![4,5,1,2,3]),some (0,![2,4,1,5,3]),none,some (0,![2,4,1,5,3]),none,
  some (0,![1,4,2,5,3]),none,some (0,![1,4,2,5,3]),none,none,none,
  none,none]
private def pairRow8 : List (Option (CW 6)) := [
  some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),
  some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),
  some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),
  some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),
  some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4]),
  some (1,![0,3,1,2,4]),some (1,![0,3,1,2,4])]
private def pairRow9 : List (Option (CW 6)) := [
  none,some (1,![0,4,1,2,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,none,
  none,some (1,![5,4,1,2,3]),none,some (1,![5,4,1,2,3]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (2,![0,1,2,4,5]),none,some (1,![0,1,2,4,5]),none,none,none,
  some (1,![0,2,1,4,5]),none,none,none,some (1,![5,3,1,2,4]),none,
  some (1,![5,3,1,2,4]),none]
private def pairRow10 : List (Option (CW 6)) := [
  none,some (0,![2,0,1,4,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (1,![0,3,2,5,4]),none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,some (1,![4,5,1,3,2]),
  some (0,![4,3,0,2,5]),none,some (0,![2,5,1,4,3]),none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (1,![0,1,2,5,4]),none,some (1,![1,0,4,5,2]),none,none,none,
  some (0,![4,1,0,2,5]),none,some (0,![1,4,3,5,2]),none,none,none,
  none,none]
private def pairRow11 : List (Option (CW 6)) := [
  none,none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,some (1,![4,5,1,3,2]),
  some (0,![2,5,1,4,3]),none,some (0,![2,5,1,4,3]),none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,none,none,none,none,none,
  some (0,![1,4,3,5,2]),none,some (0,![1,4,3,5,2]),none,none,none,
  none,none]
private def pairRow12 : List (Option (CW 6)) := [
  none,some (0,![1,0,2,4,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,some (1,![4,5,2,3,1]),some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (1,![0,3,1,5,4]),none,
  some (0,![4,3,0,1,5]),none,some (0,![1,5,2,4,3]),none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (1,![0,2,1,5,4]),none,some (0,![4,2,0,1,5]),none,some (0,![1,5,3,4,2]),none,
  some (1,![2,0,4,5,1]),none,none,none,none,none,
  none,none]
private def pairRow13 : List (Option (CW 6)) := [
  none,none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,some (1,![4,5,2,3,1]),some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,none,
  some (0,![1,5,2,4,3]),none,some (0,![1,5,2,4,3]),none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,none,some (0,![1,5,3,4,2]),none,some (0,![1,5,3,4,2]),none,
  none,none,none,none,none,none,
  none,none]
private def pairRow14 : List (Option (CW 6)) := [
  none,some (2,![4,1,2,3,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (1,![4,1,2,3,5]),none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (1,![4,2,1,3,5]),none,
  none,none,none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (1,![4,3,1,2,5]),none,none,none,none,none,
  none,none,none,none,none,none,
  none,none]
private def pairRow15 : List (Option (CW 6)) := [
  none,some (2,![4,1,2,3,5]),some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (1,![4,1,2,3,5]),none,some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (1,![4,2,1,3,5]),none,
  none,none,none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (1,![4,3,1,2,5]),none,none,none,none,none,
  none,none,none,none,none,none,
  none,none]

private def pairWitness (a b : Mask) (e : Bool) : Option (CW 6) :=
  match a.val with
  | 0 => (pairRow0[2*b.val+e.toNat]?).getD none
  | 1 => (pairRow1[2*b.val+e.toNat]?).getD none
  | 2 => (pairRow2[2*b.val+e.toNat]?).getD none
  | 3 => (pairRow3[2*b.val+e.toNat]?).getD none
  | 4 => (pairRow4[2*b.val+e.toNat]?).getD none
  | 5 => (pairRow5[2*b.val+e.toNat]?).getD none
  | 6 => (pairRow6[2*b.val+e.toNat]?).getD none
  | 7 => (pairRow7[2*b.val+e.toNat]?).getD none
  | 8 => (pairRow8[2*b.val+e.toNat]?).getD none
  | 9 => (pairRow9[2*b.val+e.toNat]?).getD none
  | 10 => (pairRow10[2*b.val+e.toNat]?).getD none
  | 11 => (pairRow11[2*b.val+e.toNat]?).getD none
  | 12 => (pairRow12[2*b.val+e.toNat]?).getD none
  | 13 => (pairRow13[2*b.val+e.toNat]?).getD none
  | 14 => (pairRow14[2*b.val+e.toNat]?).getD none
  | 15 => (pairRow15[2*b.val+e.toNat]?).getD none
  | _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem pairValid : ∀ (a b : Mask) (e : Bool), optionOK (pairCode a b e) (pairWitness a b e) := by
  intro a
  fin_cases a <;> decide

private def attachRow7 : List (Option (CW 7)) := [
  none,some (0,![3,0,4,6,5]),some (1,![4,0,5,6,3]),none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),
  some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (1,![0,4,3,5,6]),some (1,![0,5,2,3,6]),none,some (1,![0,5,2,3,6]),some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),
  some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (1,![0,4,3,5,6]),some (1,![0,5,1,3,6]),none,some (1,![0,5,1,3,6]),
  none,some (0,![3,0,1,5,6]),some (1,![4,0,5,6,3]),some (0,![3,0,1,5,6]),some (1,![0,4,3,5,6]),none,
  none,none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  none,some (1,![0,5,1,2,6]),some (1,![4,5,1,2,3]),some (1,![0,5,1,2,6]),some (0,![5,3,0,4,6]),some (0,![2,0,1,5,6]),
  some (1,![4,5,2,6,3]),some (0,![2,0,1,5,6]),some (0,![2,4,1,5,3]),some (0,![2,4,1,5,3]),some (1,![4,5,2,6,3]),none,
  some (0,![5,3,0,4,6]),some (0,![1,0,2,5,6]),some (1,![4,5,1,6,3]),some (0,![1,0,2,5,6]),some (0,![1,4,2,5,3]),some (0,![1,4,2,5,3]),
  some (1,![4,5,1,6,3]),none,some (0,![5,3,0,4,6]),some (2,![5,1,2,3,6]),none,some (2,![5,1,2,3,6]),
  some (0,![3,5,1,4,6]),some (2,![5,1,2,3,6]),none,some (2,![5,1,2,3,6])]
private def attachRow11 : List (Option (CW 7)) := [
  none,some (0,![2,0,4,6,5]),some (1,![4,0,5,6,2]),none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),
  some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  some (1,![0,4,2,5,6]),some (1,![0,5,2,3,6]),none,some (1,![0,5,2,3,6]),some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),
  some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),none,some (1,![0,5,1,3,6]),some (1,![4,5,1,3,2]),some (1,![0,5,1,3,6]),
  some (0,![5,2,0,4,6]),some (0,![3,0,1,5,6]),some (1,![4,5,3,6,2]),some (0,![3,0,1,5,6]),some (0,![2,5,1,4,3]),some (0,![2,5,1,4,3]),
  some (1,![4,5,3,6,2]),none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (1,![0,4,2,5,6]),some (1,![0,5,1,2,6]),none,some (1,![0,5,1,2,6]),none,some (0,![2,0,1,5,6]),
  some (1,![4,0,5,6,2]),some (0,![2,0,1,5,6]),some (1,![0,4,2,5,6]),none,none,none,
  some (0,![5,2,0,4,6]),some (0,![1,0,2,5,6]),some (1,![4,5,1,6,2]),some (0,![1,0,2,5,6]),some (0,![1,4,3,5,2]),some (0,![1,4,3,5,2]),
  some (1,![4,5,1,6,2]),none,some (0,![5,2,0,4,6]),some (2,![5,1,2,3,6]),none,some (2,![5,1,2,3,6]),
  some (0,![2,5,1,4,6]),some (2,![5,1,2,3,6]),none,some (2,![5,1,2,3,6])]
private def attachRow13 : List (Option (CW 7)) := [
  none,some (0,![1,0,4,6,5]),some (1,![4,0,5,6,1]),none,some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),
  some (2,![0,1,2,3,5]),some (2,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),some (1,![0,1,2,3,5]),
  none,some (1,![0,5,2,3,6]),some (1,![4,5,2,3,1]),some (1,![0,5,2,3,6]),some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),
  some (1,![0,2,1,3,5]),some (1,![0,2,1,3,5]),some (1,![0,4,1,5,6]),some (1,![0,5,1,3,6]),none,some (1,![0,5,1,3,6]),
  some (0,![5,1,0,4,6]),some (0,![3,0,1,5,6]),some (1,![4,5,3,6,1]),some (0,![3,0,1,5,6]),some (0,![1,5,2,4,3]),some (0,![1,5,2,4,3]),
  some (1,![4,5,3,6,1]),none,some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),some (1,![0,3,1,2,5]),
  some (1,![0,4,1,5,6]),some (1,![0,5,1,2,6]),none,some (1,![0,5,1,2,6]),some (0,![5,1,0,4,6]),some (0,![2,0,1,5,6]),
  some (1,![4,5,2,6,1]),some (0,![2,0,1,5,6]),some (0,![1,5,3,4,2]),some (0,![1,5,3,4,2]),some (1,![4,5,2,6,1]),none,
  none,some (0,![1,0,2,5,6]),some (1,![4,0,5,6,1]),some (0,![1,0,2,5,6]),some (1,![0,4,1,5,6]),none,
  none,none,some (0,![5,1,0,4,6]),some (2,![5,1,2,3,6]),none,some (2,![5,1,2,3,6]),
  some (0,![1,5,2,4,6]),some (2,![5,1,2,3,6]),none,some (2,![5,1,2,3,6])]

private def attachWitness (a b : Mask) (e same : Bool) : Option (CW 7) :=
  match a.val with
  | 7 => (attachRow7[4*b.val+2*e.toNat+same.toNat]?).getD none
  | 11 => (attachRow11[4*b.val+2*e.toNat+same.toNat]?).getD none
  | 13 => (attachRow13[4*b.val+2*e.toNat+same.toNat]?).getD none
  | _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem attachValid : ∀ (a b : Mask) (e same : Bool), optionOK (attachCode a b e same) (attachWitness a b e same) := by
  intro a
  fin_cases a <;> decide

private def farRow7 : List (Option (CW 7)) := [
  some (0,![3,0,4,5,6]),some (1,![4,0,5,6,3])]
private def farRow11 : List (Option (CW 7)) := [
  some (0,![2,0,4,5,6]),some (1,![4,0,5,6,2])]
private def farRow13 : List (Option (CW 7)) := [
  some (0,![1,0,4,5,6]),some (1,![4,0,5,6,1])]

private def farWitness (a : Mask) (share : Bool) : Option (CW 7) :=
  match a.val with
  | 7 => (farRow7[share.toNat]?).getD none
  | 11 => (farRow11[share.toNat]?).getD none
  | 13 => (farRow13[share.toNat]?).getD none
  | _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem farValid : ∀ (a : Mask) (share : Bool), optionOK (farCode a share) (farWitness a share) := by
  decide

private def crossRow7 : List (Option (CW 8)) := [
  none,none,none,none,none,none,
  none,none,none,none,none,none,
  none,none,some (1,![0,4,3,5,6]),none,none,none,
  none,none,none,none,some (0,![6,4,0,5,7]),some (1,![4,5,2,6,3]),
  none,none,some (0,![6,4,0,5,7]),some (1,![4,5,1,6,3]),none,none,
  none,none]
private def crossRow11 : List (Option (CW 8)) := [
  none,none,none,none,none,none,
  none,none,none,none,none,none,
  none,none,some (0,![6,4,0,5,7]),some (1,![4,5,3,6,2]),none,none,
  none,none,none,none,some (1,![0,4,2,5,6]),none,
  none,none,some (0,![6,4,0,5,7]),some (1,![4,5,1,6,2]),none,none,
  none,none]
private def crossRow13 : List (Option (CW 8)) := [
  none,none,none,none,none,none,
  none,none,none,none,none,none,
  none,none,some (0,![6,4,0,5,7]),some (1,![4,5,3,6,1]),none,none,
  none,none,none,none,some (0,![6,4,0,5,7]),some (1,![4,5,2,6,1]),
  none,none,some (1,![0,4,1,5,6]),none,none,none,
  none,none]

private def crossWitness (a b : Mask) (e : Bool) : Option (CW 8) :=
  match a.val with
  | 7 => (crossRow7[2*b.val+e.toNat]?).getD none
  | 11 => (crossRow11[2*b.val+e.toNat]?).getD none
  | 13 => (crossRow13[2*b.val+e.toNat]?).getD none
  | _ => none

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem crossValid : ∀ (a b : Mask) (e : Bool), optionOK (crossCode a b e) (crossWitness a b e) := by
  intro a
  fin_cases a <;> decide



private def vectorTwo {V : Type*} (x y : V) (h : x ≠ y) : Fin 2 ↪ V where
  toFun := ![x,y]
  inj' := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all

private def vectorThree {V : Type*} (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : Fin 3 ↪ V where
  toFun := ![x,y,z]
  inj' := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all

private def vectorFour {V : Type*} (x y z w : V) (hxy : x ≠ y) (hxz : x ≠ z)
    (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : Fin 4 ↪ V where
  toFun := ![x,y,z,w]
  inj' := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all

private theorem avoided_one {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) {x : V} (hx : Outside Q x)
    (a : Mask) (ha : HasMask G Q x a) :
    (oneWitness a).isNone = true := by
  let f : Fin 1 ↪ V := ⟨fun _ => x,fun _ _ _ => Subsingleton.elim _ _⟩
  have hOut : ∀ i, Outside Q (f i) := fun _ => hx
  have hm : ∀ i, HasMask G Q (f i) (![a] i) := by
    intro i
    fin_cases i
    exact ha
  have hE : ∀ i j, G.Adj (f i) (f j) ↔ (fun _ _ : Fin 1 => false) i j = true := by
    intro i j
    simp [f]
  exact witness_avoided h (packed Q f hOut) (oneCode a)
    (packed_agree hq f hOut _ hm _ hE) _ (oneValid a)

private theorem avoided_pair {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) {x y : V} (hx : Outside Q x) (hy : Outside Q y)
    (hxy : x ≠ y) (a b : Mask) (ha : HasMask G Q x a) (hb : HasMask G Q y b)
    (e : Bool) (he : G.Adj x y ↔ e = true) :
    (pairWitness a b e).isNone = true := by
  let f := vectorTwo x y hxy
  have hOut : ∀ i, Outside Q (f i) := by intro i; fin_cases i; exact hx; exact hy
  have hm : ∀ i, HasMask G Q (f i) (![a,b] i) := by intro i; fin_cases i; exact ha; exact hb
  have hE : ∀ i j, G.Adj (f i) (f j) ↔ edge2 e i j = true := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f,vectorTwo,edge2,G.adj_comm,he]
  exact witness_avoided h (packed Q f hOut) (pairCode a b e)
    (packed_agree hq f hOut _ hm _ hE) _ (pairValid a b e)

private theorem avoided_three {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) {x y z : V} (hx : Outside Q x) (hy : Outside Q y)
    (hz : Outside Q z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a b c : Mask) (ha : HasMask G Q x a) (hb : HasMask G Q y b) (hc : HasMask G Q z c)
    (e₁ e₂ e₃ : Bool) (he₁ : G.Adj x y ↔ e₁ = true)
    (he₂ : G.Adj x z ↔ e₂ = true) (he₃ : G.Adj y z ↔ e₃ = true)
    (w : Option (CW 7)) (hw : optionOK (packedAdj ![a,b,c] (edge3 e₁ e₂ e₃)) w) :
    w.isNone = true := by
  let f := vectorThree x y z hxy hxz hyz
  have hOut : ∀ i, Outside Q (f i) := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  have hm : ∀ i, HasMask G Q (f i) (![a,b,c] i) := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have hE : ∀ i j, G.Adj (f i) (f j) ↔ edge3 e₁ e₂ e₃ i j = true := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f,vectorThree,edge3,G.adj_comm,he₁,he₂,he₃]
  exact witness_avoided h (packed Q f hOut) _
    (packed_agree hq f hOut _ hm _ hE) _ hw

private theorem avoided_cross {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) {x y z w : V}
    (hx : Outside Q x) (hy : Outside Q y) (hz : Outside Q z) (hw : Outside Q w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w)
    (a b : Mask) (ha : HasMask G Q x a) (hb : HasMask G Q y b)
    (hc : HasMask G Q z 0) (hd : HasMask G Q w 0)
    (e : Bool) (he : G.Adj x y ↔ e = true)
    (hxZ : G.Adj x z) (hyW : G.Adj y w)
    (hxW : ¬ G.Adj x w) (hyZ : ¬ G.Adj y z) (hzW : ¬ G.Adj z w) :
    (crossWitness a b e).isNone = true := by
  let f := vectorFour x y z w hxy hxz hxw hyz hyw hzw
  have hOut : ∀ i, Outside Q (f i) := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
    · exact hw
  have hm : ∀ i, HasMask G Q (f i) (![a,b,0,0] i) := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hE : ∀ i j, G.Adj (f i) (f j) ↔ edge4 e i j = true := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f,vectorFour,edge4,G.adj_comm,he,hxZ,hyW,hxW,hyZ,hzW]
  exact witness_avoided h (packed Q f hOut) _
    (packed_agree hq f hOut _ hm _ hE) _ (crossValid a b e)

def AttachmentMask (m : Mask) : Prop := m = 7 ∨ m = 11 ∨ m = 13

instance (m : Mask) : Decidable (AttachmentMask m) := by
  unfold AttachmentMask
  infer_instance

private def maskSize (m : Mask) : ℕ :=
  ((univ : Finset (Fin 4)).filter fun i => m.val.testBit i.val).card

set_option maxRecDepth 10000 in
private theorem oneRule :
    ∀ a : Mask, a ≠ 0 → (oneWitness a).isNone = true → 2 ≤ maskSize a := by decide

set_option maxRecDepth 10000 in
private theorem attachmentRule :
    ∀ a : Mask, a ≠ 0 → (pairWitness a 0 true).isNone = true → AttachmentMask a := by decide

set_option maxRecDepth 10000 in
private theorem outsideRule :
    ∀ (b : Mask) (e : Bool), b ≠ 0 → (attachWitness 7 b e false).isNone = true →
      ((b = 6 ∨ b = 9) ∧ e = false) ∨ ((b = 3 ∨ b = 5 ∨ b = 7 ∨ b = 14 ∨ b = 15) ∧ e = true) := by
  decide

set_option maxRecDepth 10000 in
private theorem outsideMixedRule :
    ∀ (b : Mask) (e e' : Bool), b ≠ 0 → (attachWitness 7 b e false).isNone = true →
      (attachWitness 11 b e' false).isNone = true →
      ((b = 3 ∨ b = 14 ∨ b = 15) ∧ e = true ∧ e' = true) ∨
        (b = 5 ∧ e = true ∧ e' = false) ∨ (b = 9 ∧ e = false ∧ e' = true) := by
  decide

set_option maxRecDepth 10000 in
private theorem sameComponentRule :
    ∀ (a b : Mask) (e : Bool), AttachmentMask a → AttachmentMask b → a ≠ b →
      (attachWitness a b e true).isNone = true → e = true := by
  intro a
  fin_cases a <;> decide

set_option maxRecDepth 10000 in
private theorem farRule :
    ∀ (a : Mask) (share : Bool), AttachmentMask a → (farWitness a share).isNone = false := by
  decide

set_option maxRecDepth 10000 in
private theorem crossRule :
    ∀ (a b : Mask) (e : Bool), AttachmentMask a → AttachmentMask b →
      (crossWitness a b e).isNone = true → a = b ∧ e = true := by
  intro a
  fin_cases a <;> decide

private theorem mask_zero_iff {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V} {x : V} :
    HasMask G Q x 0 ↔ ∀ i, ¬ G.Adj (Q i) x := by
  simp [HasMask]

private theorem mask_ne_zero {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V} {x : V}
    {a : Mask} (ha : HasMask G Q x a) (hn : Near G Q x) : a ≠ 0 := by
  rintro rfl
  obtain ⟨i,hi⟩ := hn.2
  exact (mask_zero_iff.mp ha) i hi

private theorem near_far_ne {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V} {x y : V}
    (hx : Near G Q x) (hy : Far G Q y) : x ≠ y := by
  rintro rfl
  exact mask_ne_zero hy.2 hx rfl

open Classical in
theorem near_mask_at_least_two {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V} {x : V}
    (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x) {m : Mask}
    (hm : HasMask G Q x m) :
    2 ≤ ((univ : Finset (Fin 4)).filter fun i => G.Adj (Q i) x).card := by
  classical
  have hx' : maskSize m = ((univ : Finset (Fin 4)).filter fun i => G.Adj (Q i) x).card := by
    unfold maskSize
    congr 1
    ext i
    simp only [mem_filter,mem_univ,true_and]
    exact (hm i).symm
  rw [← hx']
  exact oneRule m (mask_ne_zero hm hx) (avoided_one h hq hx.1 m hm)

theorem near_far_attachment_mask {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x z : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x) (hz : Far G Q z)
    (he : G.Adj x z) {m : Mask} (hm : HasMask G Q x m) : AttachmentMask m := by
  exact attachmentRule m (mask_ne_zero hm hx)
    (avoided_pair h hq hx.1 hz.1 he.ne m 0 hm hz.2 true (iff_of_true he rfl))

theorem attachment_outside_pattern {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y z : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x)
    (hy : Near G Q y) (hz : Far G Q z) (hm : HasMask G Q x 7)
    (hxz : G.Adj x z) (hyz : ¬ G.Adj y z) {b : Mask} (hb : HasMask G Q y b) :
    ((b = 6 ∨ b = 9) ∧ ¬ G.Adj x y) ∨
      ((b = 3 ∨ b = 5 ∨ b = 7 ∨ b = 14 ∨ b = 15) ∧ G.Adj x y) := by
  classical
  let e := decide (G.Adj x y)
  have xy : x ≠ y := fun he => hyz (he ▸ hxz)
  have hOk := avoided_three h hq hx.1 hy.1 hz.1 xy hxz.ne (near_far_ne hy hz)
    7 b 0 hm hb hz.2 e true false (by simp [e]) (iff_of_true hxz rfl)
    (iff_of_false hyz (by decide)) _ (attachValid 7 b e false)
  have rr := outsideRule b e (mask_ne_zero hb hy) hOk
  simpa [e] using rr

theorem same_component_distinct_masks_adjacent {V : Type*} {G : SimpleGraph V}
    {Q : Fin 4 ↪ V} {x y z : V} (h : NoTree5 G) (hq : IsClaw G Q)
    (hx : Near G Q x) (hy : Near G Q y) (hz : Far G Q z)
    (hxz : G.Adj x z) (hyz : G.Adj y z)
    {a b : Mask} (ha : HasMask G Q x a) (hb : HasMask G Q y b) (hab : a ≠ b) (hxy : x ≠ y) :
    G.Adj x y := by
  classical
  let e := decide (G.Adj x y)
  have hOk := avoided_three h hq hx.1 hy.1 hz.1 hxy hxz.ne hyz.ne
    a b 0 ha hb hz.2 e true true (by simp [e]) (iff_of_true hxz rfl)
    (iff_of_true hyz rfl) _ (attachValid a b e true)
  have hm := sameComponentRule a b e (near_far_attachment_mask h hq hx hz hxz ha)
    (near_far_attachment_mask h hq hy hz hyz hb) hab hOk
  simpa [e] using hm

private theorem far_constraint {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y z : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x)
    (hy : Far G Q y) (hz : Far G Q z) (hxy : G.Adj x y) (hyz : y ≠ z)
    (share : Bool) (he₁ : G.Adj x z ↔ share = true)
    (he₂ : G.Adj y z ↔ (!share) = true) : False := by
  obtain ⟨a,ha⟩ := mask_exists G Q x
  have ht := near_far_attachment_mask h hq hx hy hxy ha
  have hOk := avoided_three h hq hx.1 hy.1 hz.1 hxy.ne (near_far_ne hx hz) hyz
    a 0 0 ha hy.2 hz.2 true share (!share) (iff_of_true hxy rfl) he₁ he₂ _
    (farValid a share)
  rw [farRule a share ht] at hOk
  cases hOk

theorem near_attachment_propagates {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y z : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x)
    (hy : Far G Q y) (hz : Far G Q z) (hxy : G.Adj x y) (hyz : G.Adj y z) :
    G.Adj x z := by
  classical
  by_cases hAdj : G.Adj x z
  · exact hAdj
  · exact (far_constraint h hq hx hy hz hxy hyz.ne false (iff_of_false hAdj (by decide))
      (iff_of_true hyz rfl)).elim

theorem far_neighbors_adjacent {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y z : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x)
    (hy : Far G Q y) (hz : Far G Q z) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hne : y ≠ z) : G.Adj y z := by
  classical
  by_cases hAdj : G.Adj y z
  · exact hAdj
  · exact (far_constraint h hq hx hy hz hxy hne true (iff_of_true hxz rfl)
      (iff_of_false hAdj (by decide))).elim

theorem different_module_attachments {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y z w : V} (h : NoTree5 G) (hq : IsClaw G Q)
    (hx : Near G Q x) (hy : Near G Q y) (hz : Far G Q z) (hw : Far G Q w)
    (hxZ : G.Adj x z) (hyW : G.Adj y w) (hxW : ¬ G.Adj x w) (hyZ : ¬ G.Adj y z)
    (hzW : ¬ G.Adj z w) {a b : Mask} (ha : HasMask G Q x a) (hb : HasMask G Q y b) :
    a = b ∧ G.Adj x y := by
  classical
  let e := decide (G.Adj x y)
  have hxy : x ≠ y := fun he => hxW (he.symm ▸ hyW)
  have hzw : z ≠ w := fun he => hxW (he ▸ hxZ)
  have hh := avoided_cross h hq hx.1 hy.1 hz.1 hw.1 hxy hxZ.ne
    (near_far_ne hx hw) (near_far_ne hy hz) hyW.ne hzw a b ha hb hz.2 hw.2 e (by simp [e])
    hxZ hyW hxW hyZ hzW
  simpa [e] using crossRule a b e (near_far_attachment_mask h hq hx hz hxZ ha)
    (near_far_attachment_mask h hq hy hw hyW hb) hh

#print axioms near_mask_at_least_two
#print axioms near_far_attachment_mask
#print axioms attachment_outside_pattern
#print axioms same_component_distinct_masks_adjacent
#print axioms near_attachment_propagates
#print axioms far_neighbors_adjacent
#print axioms different_module_attachments

theorem mixed_attachment_outside_pattern {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x x' y z : V} (h : NoTree5 G) (hq : IsClaw G Q)
    (hx : Near G Q x) (hx' : Near G Q x') (hy : Near G Q y) (hz : Far G Q z)
    (hm : HasMask G Q x 7) (hm' : HasMask G Q x' 11)
    (hxz : G.Adj x z) (hxz' : G.Adj x' z) (hyz : ¬ G.Adj y z)
    {b : Mask} (hb : HasMask G Q y b) :
    ((b = 3 ∨ b = 14 ∨ b = 15) ∧ G.Adj x y ∧ G.Adj x' y) ∨
      (b = 5 ∧ G.Adj x y ∧ ¬ G.Adj x' y) ∨ (b = 9 ∧ ¬ G.Adj x y ∧ G.Adj x' y) := by
  classical
  let e := decide (G.Adj x y)
  let e' := decide (G.Adj x' y)
  have out (s : V) (hs : Near G Q s) (ha : G.Adj s z) (m : Mask) (hM : HasMask G Q s m) :
      (attachWitness m b (decide (G.Adj s y)) false).isNone = true := by
    have hxy : s ≠ y := fun he => hyz (he ▸ ha)
    exact avoided_three h hq hs.1 hy.1 hz.1 hxy ha.ne (near_far_ne hy hz)
      m b 0 hM hb hz.2 _ true false (by simp) (iff_of_true ha rfl)
      (iff_of_false hyz (by decide)) _ (attachValid m b _ false)
  simpa [e,e'] using outsideMixedRule b e e' (mask_ne_zero hb hy)
    (out x hx hxz 7 hm) (out x' hx' hxz' 11 hm')

def CliqueMask (a : Mask) : Prop := a = 3 ∨ a = 5 ∨ a = 6 ∨ a = 9 ∨ a = 10 ∨ a = 12
def CenterLeafMask (a : Mask) : Prop := a = 3 ∨ a = 5 ∨ a = 9
def FullLeavesMask (a : Mask) : Prop := a = 14 ∨ a = 15
def LeafPairMask (a : Mask) : Prop := a = 6 ∨ a = 10 ∨ a = 12

instance (a : Mask) : Decidable (CliqueMask a) := by unfold CliqueMask; infer_instance
instance (a : Mask) : Decidable (CenterLeafMask a) := by unfold CenterLeafMask; infer_instance
instance (a : Mask) : Decidable (FullLeavesMask a) := by unfold FullLeavesMask; infer_instance
instance (a : Mask) : Decidable (LeafPairMask a) := by unfold LeafPairMask; infer_instance

private theorem cliqueMaskRule :
    ∀ a : Mask, CliqueMask a → (pairWitness a a false).isNone = false := by decide

private theorem antiRule : (pairWitness 6 9 true).isNone = false := by decide

private theorem highLowRule :
    ∀ a b : Mask, CenterLeafMask a → FullLeavesMask b → (pairWitness a b false).isNone = false := by
  intro a
  fin_cases a <;> decide

private theorem leafPairRule :
    ∀ a b : Mask, LeafPairMask a → LeafPairMask b → (pairWitness a b false).isNone = false := by
  intro a
  fin_cases a <;> decide

theorem clique_mask_pair_adjacent {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Outside Q x)
    (hy : Outside Q y) (hne : x ≠ y) {m : Mask} (hm : CliqueMask m)
    (hxM : HasMask G Q x m) (hyM : HasMask G Q y m) : G.Adj x y := by
  classical
  by_cases he : G.Adj x y
  · exact he
  · have hh := avoided_pair h hq hx hy hne m m hxM hyM false (iff_of_false he (by decide))
    rw [cliqueMaskRule m hm] at hh
    cases hh

theorem two_antipodal_masks_anticomplete {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Outside Q x)
    (hy : Outside Q y) (hxM : HasMask G Q x 6) (hyM : HasMask G Q y 9) : ¬G.Adj x y := by
  intro hh
  have he := avoided_pair h hq hx hy hh.ne 6 9 hxM hyM true (iff_of_true hh rfl)
  rw [antiRule] at he
  cases he

theorem center_leaf_full_leaves_adjacent {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Outside Q x)
    (hy : Outside Q y) (hne : x ≠ y) {m n : Mask} (hm : CenterLeafMask m) (hn : FullLeavesMask n)
    (hxM : HasMask G Q x m) (hyM : HasMask G Q y n) : G.Adj x y := by
  classical
  by_cases he : G.Adj x y
  · exact he
  · have hh := avoided_pair h hq hx hy hne m n hxM hyM false (iff_of_false he (by decide))
    rw [highLowRule m n hm hn] at hh
    cases hh

theorem leaf_pair_masks_adjacent {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Outside Q x)
    (hy : Outside Q y) (hne : x ≠ y) {m n : Mask} (hm : LeafPairMask m) (hn : LeafPairMask n)
    (hxM : HasMask G Q x m) (hyM : HasMask G Q y n) : G.Adj x y := by
  classical
  by_cases he : G.Adj x y
  · exact he
  · have hh := avoided_pair h hq hx hy hne m n hxM hyM false (iff_of_false he (by decide))
    rw [leafPairRule m n hm hn] at hh
    cases hh

def FarGraph {V : Type*} (G : SimpleGraph V) (Q : Fin 4 ↪ V) :=
  G.induce {v | Far G Q v}

/-- Adjacency to a near vertex is constant on far components. -/
theorem near_attachment_constant {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) {x : V} (hx : Near G Q x)
    {y z : {v | Far G Q v}} (hyz : (FarGraph G Q).Reachable y z) :
    G.Adj x y.val ↔ G.Adj x z.val := by
  have propagate {a b : {v | Far G Q v}} (r : (FarGraph G Q).Reachable a b)
      (ha : G.Adj x a.val) : G.Adj x b.val := by
    obtain ⟨p⟩ := r
    induction p with
    | nil => exact ha
    | @cons a c b ac p ih =>
      exact ih (near_attachment_propagates h hq hx a.property c.property ha ac)
  exact ⟨propagate hyz,propagate hyz.symm⟩

private theorem reach_far_until_boundary {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {y z : V} (p : G.Walk y z) (hy : Far G Q y) (hz : ¬ Far G Q z) :
    ∃ w : {v | Far G Q v}, ∃ x : V, Near G Q x ∧ G.Adj x w.val ∧
      (FarGraph G Q).Reachable ⟨y,hy⟩ w := by
  classical
  induction p with
  | nil => exact (hz hy).elim
  | @cons a b c ab p ih =>
    by_cases hb : Far G Q b
    · obtain ⟨w,x,hx,he,hr⟩ := ih hb hz
      have e : (FarGraph G Q).Adj ⟨a,hy⟩ ⟨b,hb⟩ := ab
      exact ⟨w,x,hx,he,e.reachable.trans hr⟩
    · have ho : Outside Q b := by
        intro i he
        exact (mask_zero_iff.mp hy.2) i (he ▸ ab.symm)
      have hn : Near G Q b := by
        refine ⟨ho,?_⟩
        by_contra! he
        exact hb ⟨ho,mask_zero_iff.mpr he⟩
      exact ⟨⟨a,hy⟩,b,hn,ab.symm,Reachable.rfl⟩

/-- Every far vertex of a connected graph has a near neighbor. -/
theorem far_has_attachment {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) (hc : G.Connected) (y : {v | Far G Q v}) :
    ∃ x : V, Near G Q x ∧ G.Adj x y.val := by
  obtain ⟨p⟩ := hc y.val (Q 0)
  obtain ⟨z,x,hx,hxz,hr⟩ := reach_far_until_boundary p y.property
    (fun hh => hh.1 0 rfl)
  exact ⟨x,hx,(near_attachment_constant h hq hx hr).mpr hxz⟩

theorem far_component_clique {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) (hc : G.Connected)
    {y z : {v | Far G Q v}} (hr : (FarGraph G Q).Reachable y z) (hne : y ≠ z) :
    G.Adj y.val z.val := by
  obtain ⟨x,hx,hxy⟩ := far_has_attachment h hq hc y
  exact far_neighbors_adjacent h hq hx y.property z.property hxy
    ((near_attachment_constant h hq hx hr).mp hxy) (fun he => hne (Subtype.ext he))

/-- With vertex connectivity at least two, a far component has two attachments. -/
theorem far_has_two_attachments {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (h : NoTree5 G) (hq : IsClaw G Q) (hc : G.Connected) (hk : ConnectivityAtLeast G 2)
    (y : {v | Far G Q v}) :
    ∃ x z : V, x ≠ z ∧ Near G Q x ∧ Near G Q z ∧ G.Adj x y.val ∧ G.Adj z y.val := by
  classical
  obtain ⟨x,hx,hxy⟩ := far_has_attachment h hq hc y
  by_cases hSecond : ∃ z, z ≠ x ∧ Near G Q z ∧ G.Adj z y.val
  · obtain ⟨z,hz,hzn,hzy⟩ := hSecond
    exact ⟨x,z,hz.symm,hx,hzn,hxy,hzy⟩
  push_neg at hSecond
  let S : Finset V := {x}
  let H := G.induce ((↑S : Set V)ᶜ)
  have hC : H.Connected := hk.2 S (by simp [S])
  have hY : y.val ∈ (↑S : Set V)ᶜ := by simpa [S] using hxy.ne.symm
  have hQ : Q 0 ∈ (↑S : Set V)ᶜ := by simpa [S] using (hx.1 0).symm
  obtain ⟨p⟩ := hC ⟨y.val,hY⟩ ⟨Q 0,hQ⟩
  let R (v : {w : V // w ∈ (↑S : Set V)ᶜ}) : Prop :=
    ∃ hv : Far G Q v.val, (FarGraph G Q).Reachable y ⟨v.val,hv⟩
  have closed ⦃u v : {w : V // w ∈ (↑S : Set V)ᶜ}⦄ (hu : R u) (ha : H.Adj u v) : R v := by
    obtain ⟨hu,hr⟩ := hu
    by_cases hv : Far G Q v.val
    · have he : (FarGraph G Q).Adj ⟨u.val,hu⟩ ⟨v.val,hv⟩ := ha
      exact ⟨hv,hr.trans he.reachable⟩
    · have he : G.Adj u.val v.val := ha
      have ho : Outside Q v.val := by
        intro i heq
        exact (mask_zero_iff.mp hu.2) i (heq ▸ he.symm)
      have hn : Near G Q v.val := by
        refine ⟨ho,?_⟩
        by_contra! hh
        exact hv ⟨ho,mask_zero_iff.mpr hh⟩
      have h' : v.val ≠ x := by simpa [S] using v.property
      exact (hSecond v.val h' hn ((near_attachment_constant h hq hn hr).mpr he.symm)).elim
  have travel {u v : {w : V // w ∈ (↑S : Set V)ᶜ}} (p : H.Walk u v) (hu : R u) : R v := by
    induction p with
    | nil => exact hu
    | cons ha p ih => exact ih (closed hu ha)
  obtain ⟨hbad,_⟩ := travel p ⟨y.property,Reachable.rfl⟩
  exact (hbad.1 0 rfl).elim

/-- Attachments of different far components are adjacent and have the same claw mask. -/
theorem attachments_of_distinct_far_components {V : Type*} {G : SimpleGraph V}
    {Q : Fin 4 ↪ V} (h : NoTree5 G) (hq : IsClaw G Q)
    {y z : {v | Far G Q v}} (hr : ¬ (FarGraph G Q).Reachable y z)
    {x w : V} (hx : Near G Q x) (hw : Near G Q w)
    (hxy : G.Adj x y.val) (hwz : G.Adj w z.val)
    {a b : Mask} (ha : HasMask G Q x a) (hb : HasMask G Q w b) :
    a = b ∧ G.Adj x w := by
  have hyz : y.val ≠ z.val := fun he => hr (Subtype.ext he ▸ Reachable.rfl)
  have hzW : ¬ G.Adj y.val z.val := fun he => hr ⟨.cons he .nil⟩
  have hxz : ¬ G.Adj x z.val := fun he =>
    hzW (far_neighbors_adjacent h hq hx y.property z.property hxy he hyz)
  have hwy : ¬ G.Adj w y.val := fun he =>
    hzW (far_neighbors_adjacent h hq hw y.property z.property he hwz hyz)
  exact different_module_attachments h hq hx hw y.property z.property hxy hwz hxz hwy hzW ha hb

/-- The catalogue's bound at connectivity two yields clique far components with at least
two common attachments. The second conclusion holds whenever the two vertices are distinct. -/
theorem treeNumber_le_four_far_component_structure {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Fin 4 ↪ V} (ht : treeNumber G ≤ 4) (hq : IsClaw G Q)
    (hc : G.Connected) (hk : ConnectivityAtLeast G 2) (y : {v | Far G Q v}) :
    (∃ x w : V, x ≠ w ∧ Near G Q x ∧ Near G Q w ∧
      ∀ z : {v | Far G Q v}, (FarGraph G Q).Reachable y z →
        G.Adj x z.val ∧ G.Adj w z.val) ∧
    (∀ z : {v | Far G Q v}, (FarGraph G Q).Reachable y z → y ≠ z →
      (FarGraph G Q).Adj y z) := by
  have h := noTree5_of_treeNumber_le_four ht
  refine ⟨?_,fun z r hne => far_component_clique h hq hc r hne⟩
  obtain ⟨x,w,hne,hx,hw,hxy,hwy⟩ := far_has_two_attachments h hq hc hk y
  exact ⟨x,w,hne,hx,hw,fun z r =>
    ⟨(near_attachment_constant h hq hx r).mp hxy,(near_attachment_constant h hq hw r).mp hwy⟩⟩

#print axioms mixed_attachment_outside_pattern
#print axioms clique_mask_pair_adjacent
#print axioms two_antipodal_masks_anticomplete
#print axioms center_leaf_full_leaves_adjacent
#print axioms near_attachment_constant
#print axioms far_component_clique
#print axioms far_has_two_attachments
#print axioms attachments_of_distinct_far_components
#print axioms treeNumber_le_four_far_component_structure

open scoped BigOperators

def EveryClawDominates {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (Q : Fin 4 ↪ V), IsClaw G Q → ∀ x, Outside Q x → ∃ i, G.Adj (Q i) x

def IndependentFour {V : Type*} (G : SimpleGraph V) (I : Fin 4 ↪ V) : Prop :=
  ∀ i j, ¬ G.Adj (I i) (I j)

private noncomputable def adjCount {V : Type*} (G : SimpleGraph V)
    (P : Fin 4 ↪ V) (x : V) : ℕ := by
  classical
  exact ∑ i : Fin 4, if G.Adj x (P i) then 1 else 0

open Classical in
private theorem adjCount_card {V : Type*} (G : SimpleGraph V) (P : Fin 4 ↪ V) (x : V) :
    adjCount G P x = ((univ : Finset (Fin 4)).filter fun i => G.Adj (P i) x).card := by
  unfold adjCount
  simp only [G.adj_comm x, Finset.sum_boole, Nat.cast_id]

private theorem adjCount_eq_maskSize {V : Type*} {G : SimpleGraph V} {P : Fin 4 ↪ V} {x : V}
    {m : Mask} (hm : HasMask G P x m) : adjCount G P x = maskSize m := by
  classical
  rw [adjCount_card,maskSize]
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  exact hm i

private noncomputable def eqCount {V : Type*} (P : Fin 4 ↪ V) (x : V) : ℕ := by
  classical
  exact ∑ i : Fin 4, if x = P i then 1 else 0

private theorem eqCount_formula {V : Type*} (P : Fin 4 ↪ V) (x : V) :
    eqCount P x = 0 ∧ Outside P x ∨ eqCount P x = 1 ∧ ∃ i, x = P i := by
  classical
  by_cases hx : Outside P x
  · exact Or.inl ⟨by simp [eqCount, Outside] at hx ⊢; simp [hx],hx⟩
  · unfold Outside at hx
    push_neg at hx
    obtain ⟨i,rfl⟩ := hx
    exact Or.inr ⟨by simp [eqCount,P.injective.eq_iff],i,rfl⟩

private theorem threeBits_and_spare :
    ∀ m : Mask, 2 < maskSize m → ∃ i j k l : Fin 4,
      i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      m.val.testBit i.val = true ∧ m.val.testBit j.val = true ∧ m.val.testBit k.val = true := by
  decide

private theorem adjCount_to_independent_four {V : Type*} {G : SimpleGraph V}
    (h : NoTree5 G) (hd : EveryClawDominates G)
    (I : Fin 4 ↪ V) (hI : IndependentFour G I) (x : V) : adjCount G I x ≤ 2 := by
  classical
  obtain ⟨m,hm⟩ := mask_exists G I x
  rw [adjCount_eq_maskSize hm]
  by_cases he : maskSize m ≤ 2
  · exact he
  obtain ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,hia,hja,hka⟩ :=
    threeBits_and_spare m (by omega)
  have hi := ((hm i).mpr hia).symm
  have hj := ((hm j).mpr hja).symm
  have hk := ((hm k).mpr hka).symm
  let Q := vectorFour x (I i) (I j) (I k) hi.ne hj.ne hk.ne
    (I.injective.ne hij) (I.injective.ne hik) (I.injective.ne hjk)
  have hQ : IsClaw G Q := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Q,vectorFour,clawAdj,hi,hj,hk,hi.symm,hj.symm,hk.symm,show ∀ i j, ¬ G.Adj (I i) (I j) from hI]
  have hN : I l ≠ x := by
    intro he'
    exact hI l i (he'.symm ▸ hi)
  have ho : Outside Q (I l) := by
    intro a
    fin_cases a
    · exact hN
    · exact I.injective.ne hil.symm
    · exact I.injective.ne hjl.symm
    · exact I.injective.ne hkl.symm
  obtain ⟨a,ha⟩ := hd Q hQ (I l) ho
  obtain ⟨b,hb⟩ := mask_exists G Q (I l)
  have htwo := near_mask_at_least_two h hQ ⟨ho,⟨a,ha⟩⟩ hb
  have hs : ((univ : Finset (Fin 4)).filter fun i => G.Adj (Q i) (I l)) ⊆ {0} := by
    intro a ha
    have hh := (mem_filter.mp ha).2
    fin_cases a <;> simp [Q,vectorFour,show ∀ i j, ¬ G.Adj (I i) (I j) from hI] at hh ⊢
  have hle := card_le_card hs
  simp only [card_singleton] at hle
  omega

private theorem claw_has_neighbor : ∀ i : Fin 4, ∃ j, clawAdj i j = true := by decide

private theorem leaf_pair_from_size :
    ∀ m : Mask, maskSize m = 2 → m.val.testBit 0 = false → LeafPairMask m := by decide

/-- If every claw dominates, the existence of one claw forces independence
number at most three under the five-vertex tree restriction. -/
theorem dominating_claw_excludes_independent_four {V : Type*} {G : SimpleGraph V}
    (h : NoTree5 G) (hd : EveryClawDominates G)
    (Q : Fin 4 ↪ V) (hq : IsClaw G Q)
    (I : Fin 4 ↪ V) (hI : IndependentFour G I) : False := by
  classical
  have rowLe (i : Fin 4) := adjCount_to_independent_four h hd I hI (Q i)
  have row (i : Fin 4) : adjCount G I (Q i) + 2 * eqCount I (Q i) ≤ 2 := by
    rcases eqCount_formula I (Q i) with ⟨he,_⟩ | ⟨he,j,hj⟩
    · simpa [he] using rowLe i
    · have hzero : adjCount G I (Q i) = 0 := by
        simp [adjCount,hj,show ∀ i j, ¬ G.Adj (I i) (I j) from hI]
      simp [hzero,he]
  have col (i : Fin 4) : 2 ≤ adjCount G Q (I i) + eqCount Q (I i) := by
    rcases eqCount_formula Q (I i) with ⟨he,ho⟩ | ⟨he,j,hj⟩
    · have hn := hd Q hq (I i) ho
      obtain ⟨m,hm⟩ := mask_exists G Q (I i)
      rw [he,add_zero,adjCount_card]
      exact near_mask_at_least_two h hq ⟨ho,hn⟩ hm
    · obtain ⟨a,ha⟩ := claw_has_neighbor j
      have hA : G.Adj (I i) (Q a) := hj.symm ▸ (hq j a).mpr ha
      have hsum := Finset.single_le_sum (s := (univ : Finset (Fin 4)))
        (f := fun u => if G.Adj (I i) (Q u) then (1 : ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ a)
      simp only [if_pos hA] at hsum
      rw [he]
      have hh : 1 ≤ adjCount G Q (I i) := hsum
      omega
  have eqA : (∑ i, adjCount G I (Q i)) = ∑ j, adjCount G Q (I j) := by
    unfold adjCount
    rw [Finset.sum_comm]
    simp [G.adj_comm]
  have eqE : (∑ i, eqCount I (Q i)) = ∑ j, eqCount Q (I j) := by
    unfold eqCount
    rw [Finset.sum_comm]
    simp [eq_comm]
  have rowSum : (∑ i, adjCount G I (Q i)) + 2 * (∑ i, eqCount I (Q i)) ≤ 8 := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _i : Fin 4, (2 : ℕ) := Finset.sum_le_sum (fun i _ => row i)
      _ = _ := by decide
  have colSum : 8 ≤ (∑ i, adjCount G Q (I i)) + (∑ i, eqCount Q (I i)) := by
    rw [← Finset.sum_add_distrib]
    calc
      8 = ∑ _i : Fin 4, (2 : ℕ) := by decide
      _ ≤ _ := Finset.sum_le_sum (fun i _ => col i)
  have hzero : (∑ i, eqCount Q (I i)) = 0 := by omega
  have disj (i : Fin 4) : Outside Q (I i) := by
    rcases eqCount_formula Q (I i) with ⟨_,ho⟩ | ⟨he,_⟩
    · exact ho
    · have hh := Finset.single_le_sum (s := (univ : Finset (Fin 4)))
        (f := fun i => eqCount Q (I i)) (fun _ _ => Nat.zero_le _) (mem_univ i)
      change eqCount Q (I i) ≤ ∑ i, eqCount Q (I i) at hh
      omega
  have heq (i : Fin 4) : eqCount Q (I i) = 0 := by
    have hn : ∀ j, I i ≠ Q j := disj i
    simp [eqCount,hn]
  have hcLe (i : Fin 4) : 2 ≤ adjCount G Q (I i) := by simpa [heq i] using col i
  have htot : (∑ i, adjCount G Q (I i)) = 8 := by omega
  have center : adjCount G I (Q 0) = 2 := by
    by_cases hc : adjCount G I (Q 0) = 2
    · exact hc
    have ht : adjCount G I (Q 0) < 2 := lt_of_le_of_ne (rowLe 0) hc
    have hsum : (∑ i, adjCount G I (Q i)) < ∑ _i : Fin 4, (2 : ℕ) :=
      Finset.sum_lt_sum (fun i _ => rowLe i) ⟨0,mem_univ _,ht⟩
    have hconst : (∑ _i : Fin 4, (2 : ℕ)) = 8 := by decide
    omega
  have size_col (i : Fin 4) : adjCount G Q (I i) = 2 := by
    by_cases hi : adjCount G Q (I i) = 2
    · exact hi
    have ht : 2 < adjCount G Q (I i) := lt_of_le_of_ne (hcLe i) (Ne.symm hi)
    have hsum : (∑ _i : Fin 4, (2 : ℕ)) < ∑ i, adjCount G Q (I i) :=
      Finset.sum_lt_sum (fun i _ => hcLe i) ⟨i,mem_univ _,ht⟩
    have hconst : (∑ _i : Fin 4, (2 : ℕ)) = 8 := by decide
    omega
  let B := (univ : Finset (Fin 4)).filter (fun i => ¬ G.Adj (Q 0) (I i))
  have hB : B.card = 2 := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Fin 4))) (p := fun i => G.Adj (Q 0) (I i))
    have hh : ((univ : Finset (Fin 4)).filter fun i => G.Adj (Q 0) (I i)).card = 2 := by
      rw [← center,adjCount_card]
      congr 1
      ext i
      simp [G.adj_comm]
    rw [hh] at h
    change 2 + B.card = (univ : Finset (Fin 4)).card at h
    simp at h
    omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
  have leafMask (a : Fin 4) (ha : a ∈ B) : ∃ m : Mask, HasMask G Q (I a) m ∧ LeafPairMask m := by
    obtain ⟨m,hm⟩ := mask_exists G Q (I a)
    refine ⟨m,hm,leaf_pair_from_size m ?_ ?_⟩
    · rw [← adjCount_eq_maskSize hm,size_col]
    · have hn := (mem_filter.mp ha).2
      have hne := mt (hm 0).mpr hn
      exact Bool.eq_false_iff.mpr hne
  obtain ⟨m,hm,hma⟩ := leafMask i hi
  obtain ⟨n,hn,hna⟩ := leafMask j hj
  exact hI i j (leaf_pair_masks_adjacent h hq (disj i) (disj j) (I.injective.ne hij) hma hna hm hn)

/-- The dominating-claw branch excludes an independent four-set under the catalogue's tree bound. -/
theorem treeNumber_le_four_excludes_independent_four_of_dominating_claws
    {V : Type*} [Fintype V] {G : SimpleGraph V} (ht : treeNumber G ≤ 4)
    (hd : EveryClawDominates G) (Q : Fin 4 ↪ V) (hq : IsClaw G Q) :
    ∀ I : Fin 4 ↪ V, ¬ IndependentFour G I :=
  fun I => dominating_claw_excludes_independent_four (noTree5_of_treeNumber_le_four ht) hd Q hq I

#print axioms noTree5_of_treeNumber_le_four
#print axioms dominating_claw_excludes_independent_four
#print axioms treeNumber_le_four_excludes_independent_four_of_dominating_claws


/-- Four independent neighbors force an induced five-vertex star. -/
theorem no_four_independent_neighbors {V : Type*} {G : SimpleGraph V}
    (h : NoTree5 G) {c a b d e : V}
    (ha : G.Adj c a) (hb : G.Adj c b) (hd : G.Adj c d) (he : G.Adj c e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (nab : ¬ G.Adj a b) (nad : ¬ G.Adj a d) (nae : ¬ G.Adj a e)
    (nbd : ¬ G.Adj b d) (nbe : ¬ G.Adj b e) (nde : ¬ G.Adj d e) : False := by
  let f : Fin 5 → V := ![c,a,b,d,e]
  have inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact ((by simpa [f] using hij) : False).elim
      | exact (ha.ne (by simpa [f] using hij)).elim
      | exact (hb.ne (by simpa [f] using hij)).elim
      | exact (hd.ne (by simpa [f] using hij)).elim
      | exact (he.ne (by simpa [f] using hij)).elim
      | exact (ha.ne (by simpa [f] using hij.symm)).elim
      | exact (hb.ne (by simpa [f] using hij.symm)).elim
      | exact (hd.ne (by simpa [f] using hij.symm)).elim
      | exact (he.ne (by simpa [f] using hij.symm)).elim
      | exact (hab (by simpa [f] using hij)).elim
      | exact (had (by simpa [f] using hij)).elim
      | exact (hae (by simpa [f] using hij)).elim
      | exact (hbd (by simpa [f] using hij)).elim
      | exact (hbe (by simpa [f] using hij)).elim
      | exact (hde (by simpa [f] using hij)).elim
      | exact (hab (by simpa [f] using hij.symm)).elim
      | exact (had (by simpa [f] using hij.symm)).elim
      | exact (hae (by simpa [f] using hij.symm)).elim
      | exact (hbd (by simpa [f] using hij.symm)).elim
      | exact (hbe (by simpa [f] using hij.symm)).elim
      | exact (hde (by simpa [f] using hij.symm)).elim

  have nba : ¬ G.Adj b a := fun n => nab n.symm
  have nda : ¬ G.Adj d a := fun n => nad n.symm
  have nea : ¬ G.Adj e a := fun n => nae n.symm
  have ndb : ¬ G.Adj d b := fun n => nbd n.symm
  have neb : ¬ G.Adj e b := fun n => nbe n.symm
  have ned : ¬ G.Adj e d := fun n => nde n.symm
  apply h 2 ⟨f,inj⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f,shapeAdj,ha,hb,hd,he,ha.symm,hb.symm,hd.symm,he.symm,nab,nad,nae,nbd,nbe,nde,
      nba,nda,nea,ndb,neb,ned]

theorem HasMask.unique {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V} {x : V}
    {a b : Mask} (ha : HasMask G Q x a) (hb : HasMask G Q x b) : a = b := by
  have check : ∀ (a b : Mask), (∀ i : Fin 4,
      a.val.testBit i.val = true ↔ b.val.testBit i.val = true) → a = b := by
    intro a
    fin_cases a <;> decide
  exact check a b (fun i => (ha i).symm.trans (hb i))



private theorem extra_attachment_rule :
    ∀ (a b : Mask) (e : Bool), AttachmentMask a →
      (attachWitness a b e false).isNone = true →
      (FullLeavesMask b → e = true) ∧
      (∀ i : Fin 4, i ≠ 0 → CenterLeafMask b → b.val.testBit i.val = true →
        (e = true ↔ a.val.testBit i.val = true)) := by
  intro a
  fin_cases a <;> decide

/-- Full-leaf masks join every attachment. A center-leaf mask joins exactly
the attachments that touch that leaf. -/
theorem extra_attachment_adjacency {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    {x y z : V} (h : NoTree5 G) (hq : IsClaw G Q) (hx : Near G Q x)
    (hy : Near G Q y) (hz : Far G Q z) (hxz : G.Adj x z) (hyz : ¬ G.Adj y z)
    {a b : Mask} (ha : HasMask G Q x a) (hb : HasMask G Q y b) :
    (FullLeavesMask b → G.Adj x y) ∧
      (∀ i : Fin 4, i ≠ 0 → CenterLeafMask b → b.val.testBit i.val = true →
        (G.Adj x y ↔ a.val.testBit i.val = true)) := by
  classical
  let e := decide (G.Adj x y)
  have hxy : x ≠ y := fun he => hyz (he ▸ hxz)
  have hOk := avoided_three h hq hx.1 hy.1 hz.1 hxy hxz.ne (near_far_ne hy hz)
    a b 0 ha hb hz.2 e true false (by simp [e]) (iff_of_true hxz rfl)
    (iff_of_false hyz (by decide)) _ (attachValid a b e false)
  simpa only [e,decide_eq_true_eq] using
    extra_attachment_rule a b e (near_far_attachment_mask h hq hx hz hxz ha) hOk

/-- Reorder the leaves of a claw while keeping its center fixed. -/
theorem isClaw_relabel {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}
    (hq : IsClaw G Q) (e : Equiv.Perm (Fin 4)) (h0 : e 0 = 0) :
    IsClaw G (e.toEmbedding.trans Q) := by
  intro i j
  change G.Adj (Q (e i)) (Q (e j)) ↔ clawAdj i j = true
  rw [hq]
  have he (i : Fin 4) : e i = 0 ↔ i = 0 := by
    exact ⟨fun h => e.injective (h.trans h0.symm),fun h => h.symm ▸ h0⟩
  simp only [clawAdj,decide_eq_true_eq,Fin.val_eq_zero_iff,Fin.val_pos_iff,
    Fin.pos_iff_ne_zero,ne_eq,he]

end Graffiti199K2

namespace Graffiti199K2
open SimpleGraph

/-- A spanning path in the sense of the catalogue. -/
def Traceable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ x, x ∈ p.support

private theorem walk_of_chain {V : Type*} {G : SimpleGraph V}
    (x : V) (l : List V) (h : List.Chain' G.Adj (x :: l)) :
    ∃ y, ∃ p : G.Walk x y, p.support = x :: l := by
  induction l generalizing x with
  | nil => exact ⟨x,.nil,rfl⟩
  | cons a l ih =>
    obtain ⟨y,p,hp⟩ := ih a h.tail
    exact ⟨y,.cons h.rel_head p,by simp [hp]⟩

theorem traceable_of_spanning_chain {V : Type*} {G : SimpleGraph V} (l : List V)
    (hn : l ≠ []) (hc : List.Chain' G.Adj l) (hd : l.Nodup) (hs : ∀ v, v ∈ l) :
    Traceable G := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons x l =>
    obtain ⟨y,p,hp⟩ := walk_of_chain x l hc
    exact ⟨x,y,p,Walk.IsPath.mk' (hp ▸ hd),fun v => hp ▸ hs v⟩

private def Good {V : Type*} (G : SimpleGraph V) (l : List V) : Prop :=
  l ≠ [] ∧ List.Chain' G.Adj l

private theorem good_reverse {V : Type*} {G : SimpleGraph V} {l : List V}
    (h : Good G l) : Good G l.reverse := by
  refine ⟨by simpa using h.1,List.chain'_reverse.mpr ?_⟩
  exact List.Chain'.imp (fun _ _ he => he.symm) h.2

private theorem good_append {V : Type*} {G : SimpleGraph V} {l r : List V}
    (h : Good G l) (k : Good G r) (he : G.Adj (l.getLast h.1) (r.head k.1)) :
    Good G (l ++ r) := by
  refine ⟨List.append_ne_nil_of_left_ne_nil h.1 r,h.2.append k.2 ?_⟩
  simpa only [List.getLast?_eq_getLast h.1,List.head?_eq_head k.1,Option.mem_some_iff]
    using (fun x (hx : l.getLast h.1 = x) y (hy : r.head k.1 = y) =>
      hx ▸ hy ▸ he)

private structure Cover {V : Type*} (G : SimpleGraph V) (S : Set V) (L : List (List V)) : Prop where
  good : ∀ l ∈ L, Good G l
  nodup : L.flatten.Nodup
  mem : ∀ x, x ∈ L.flatten ↔ x ∈ S

private theorem cover_perm {V : Type*} {G : SimpleGraph V} {S : Set V} {L M : List (List V)}
    (h : Cover G S L) (hp : L.Perm M) : Cover G S M :=
  ⟨fun l hl => h.good l (hp.mem_iff.mpr hl), hp.flatten.nodup_iff.mp h.nodup,
    fun _ => hp.flatten.mem_iff.symm.trans (h.mem _)⟩

private theorem cover_exists {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    ∃ L, Cover G S L := by
  classical
  let s : Finset V := Finset.univ.filter (· ∈ S)
  let L := s.toList.map fun x => [x]
  have hflat : L.flatten = s.toList := by
    have hh (l : List V) : (l.map fun x => [x]).flatten = l := by
      induction l with
      | nil => rfl
      | cons x l ih => simp [ih]
    exact hh _
  refine ⟨L,?_,hflat ▸ s.nodup_toList,?_⟩
  · intro p hp
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
    simp [Good]
  · intro x
    simp [hflat,s]

private theorem cover_merge_heads {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : List V} {R : List (List V)}
    (h : Cover G S (a :: b :: R)) (ha : a ≠ []) (hb : b ≠ [])
    (had : G.Adj (a.head ha) (b.head hb)) :
    Cover G S ((a.reverse ++ b) :: R) := by
  have hA := good_reverse (h.good a (by simp))
  have hB := h.good b (by simp)
  have hperm : ((a.reverse ++ b) :: R).flatten.Perm (a :: b :: R).flatten := by
    simp only [List.flatten_cons,List.append_assoc]
    exact (List.reverse_perm a).append_right _
  refine ⟨?_,hperm.nodup_iff.mpr h.nodup,fun _ => hperm.mem_iff.trans (h.mem _)⟩
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact good_append hA hB (by simpa only [List.getLast_reverse] using had)
  · exact h.good l (by simp [hl])

/-- No independent triple lies in the region. -/
def NoIndependentTriple {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x y z⦄, x ∈ S → y ∈ S → z ∈ S → x ≠ y → x ≠ z → y ≠ z →
    G.Adj x y ∨ G.Adj x z ∨ G.Adj y z

/-- Every finite region without an independent triple has a cover by at most two paths. -/
theorem two_path_cover {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hi : NoIndependentTriple G S) :
    ∃ L : List (List V), L.length ≤ 2 ∧
      (∀ l ∈ L, l ≠ [] ∧ List.Chain' G.Adj l) ∧ L.flatten.Nodup ∧
      (∀ x, x ∈ L.flatten ↔ x ∈ S) := by
  classical
  letI : DecidableEq (List V) := Classical.decEq _
  letI : BEq (List V) := instBEqOfDecidableEq
  let P (n : ℕ) := ∃ L : List (List V), L.length = n ∧ Cover G S L
  have hex : ∃ n, P n := by
    obtain ⟨L,hL⟩ := cover_exists G S
    exact ⟨L.length,L,rfl,hL⟩
  obtain ⟨L,hLen,hC⟩ := Nat.find_spec hex
  suffices h : L.length ≤ 2 from ⟨L,h,hC.good,hC.nodup,hC.mem⟩
  have pair (a b : List V) (ha : a ∈ L) (hb : b ∈ L) (hn : a ≠ b) :
      ¬ G.Adj (a.head (hC.good a ha).1) (b.head (hC.good b hb).1) := by
    intro he
    have hb' := (List.mem_erase_of_ne hn.symm).mpr hb
    have hperm := (List.perm_cons_erase ha).trans (.cons a (List.perm_cons_erase hb'))
    have hmerged := cover_merge_heads (cover_perm hC hperm) _ _ he
    have hsmall : (((a.reverse ++ b) :: (L.erase a).erase b).length) < Nat.find hex := by
      have hpLen := hperm.length_eq
      simp only [List.length_cons] at hpLen ⊢
      omega
    exact (Nat.not_lt_of_ge (Nat.find_min' hex ⟨_,rfl,hmerged⟩)) hsmall
  cases L with
  | nil => simp
  | cons a L =>
    cases L with
    | nil => simp
    | cons b L =>
      cases L with
      | nil => simp
      | cons c R =>
        let L := a :: b :: c :: R
        have ha : a ∈ L := by simp [L]
        have hb : b ∈ L := by simp [L]
        have hc : c ∈ L := by simp [L]
        let x := a.head (hC.good a ha).1
        let y := b.head (hC.good b hb).1
        let z := c.head (hC.good c hc).1
        have hx : x ∈ a := List.head_mem _
        have hy : y ∈ b := List.head_mem _
        have hz : z ∈ c := List.head_mem _
        have hd := (List.nodup_flatten.mp hC.nodup).2
        have hab : List.Disjoint a b := List.rel_of_pairwise_cons hd (by simp)
        have hac : List.Disjoint a c := List.rel_of_pairwise_cons hd (by simp)
        have hbc : List.Disjoint b c :=
          List.rel_of_pairwise_cons (List.pairwise_cons.mp hd).2 (by simp)
        have sx := (hC.mem x).mp (List.mem_flatten.mpr ⟨a,ha,hx⟩)
        have sy := (hC.mem y).mp (List.mem_flatten.mpr ⟨b,hb,hy⟩)
        have sz := (hC.mem z).mp (List.mem_flatten.mpr ⟨c,hc,hz⟩)
        have nxy : x ≠ y := fun h => hab hx (h.symm ▸ hy)
        have nxz : x ≠ z := fun h => hac hx (h.symm ▸ hz)
        have nyz : y ≠ z := fun h => hbc hy (h.symm ▸ hz)
        have nab : a ≠ b := fun h => hab hx (h ▸ hx)
        have nac : a ≠ c := fun h => hac hx (h ▸ hx)
        have nbc : b ≠ c := fun h => hbc hy (h ▸ hy)
        rcases hi sx sy sz nxy nxz nyz with h | h | h
        · exact (pair a b ha hb nab h).elim
        · exact (pair a c ha hc nac h).elim
        · exact (pair b c hb hc nbc h).elim


/-- A nonempty path traversing precisely the specified vertices. -/
structure PathOn {V : Type*} (G : SimpleGraph V) (S : Set V) where
  vertices : List V
  ne_nil : vertices ≠ []
  chain : List.Chain' G.Adj vertices
  nodup : vertices.Nodup
  mem_iff : ∀ x, x ∈ vertices ↔ x ∈ S

namespace PathOn
variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

def first (p : PathOn G A) : V := p.vertices.head p.ne_nil
def last (p : PathOn G A) : V := p.vertices.getLast p.ne_nil

theorem first_mem (p : PathOn G A) : p.first ∈ A := (p.mem_iff _).mp (List.head_mem _)
theorem last_mem (p : PathOn G A) : p.last ∈ A := (p.mem_iff _).mp (List.getLast_mem _)

def cast (p : PathOn G A) (h : A = B) : PathOn G B :=
  { p with mem_iff := fun x => h ▸ p.mem_iff x }

@[simp] theorem first_cast (p : PathOn G A) (h : A = B) : (p.cast h).first = p.first := rfl
@[simp] theorem last_cast (p : PathOn G A) (h : A = B) : (p.cast h).last = p.last := rfl

def singleton (x : V) : PathOn G ({x} : Set V) where
  vertices := [x]
  ne_nil := by simp
  chain := by simp
  nodup := by simp
  mem_iff := by simp

@[simp] theorem first_singleton (x : V) : (singleton (G := G) x).first = x := rfl
@[simp] theorem last_singleton (x : V) : (singleton (G := G) x).last = x := rfl

def reverse (p : PathOn G A) : PathOn G A where
  vertices := p.vertices.reverse
  ne_nil := (good_reverse ⟨p.ne_nil,p.chain⟩).1
  chain := (good_reverse ⟨p.ne_nil,p.chain⟩).2
  nodup := (List.reverse_perm _).nodup_iff.mpr p.nodup
  mem_iff := fun x => (List.reverse_perm _).mem_iff.trans (p.mem_iff x)

@[simp] theorem first_reverse (p : PathOn G A) : p.reverse.first = p.last :=
  List.head_reverse _
@[simp] theorem last_reverse (p : PathOn G A) : p.reverse.last = p.first :=
  List.getLast_reverse _

def join (p : PathOn G A) (q : PathOn G B) (h : Disjoint A B)
    (he : G.Adj p.last q.first) : PathOn G (A ∪ B) where
  vertices := p.vertices ++ q.vertices
  ne_nil := (good_append ⟨p.ne_nil,p.chain⟩ ⟨q.ne_nil,q.chain⟩ he).1
  chain := (good_append ⟨p.ne_nil,p.chain⟩ ⟨q.ne_nil,q.chain⟩ he).2
  nodup := List.nodup_append.mpr ⟨p.nodup,q.nodup,
    fun _ hx hy => Set.disjoint_left.mp h ((p.mem_iff _).mp hx) ((q.mem_iff _).mp hy)⟩
  mem_iff := fun x => by simp [p.mem_iff,q.mem_iff]

@[simp] theorem first_join (p : PathOn G A) (q : PathOn G B) (h : Disjoint A B)
    (he : G.Adj p.last q.first) : (p.join q h he).first = p.first :=
  List.head_append_of_ne_nil p.ne_nil

@[simp] theorem last_join (p : PathOn G A) (q : PathOn G B) (h : Disjoint A B)
    (he : G.Adj p.last q.first) : (p.join q h he).last = q.last :=
  List.getLast_append_of_ne_nil _ q.ne_nil

theorem traceable (p : PathOn G (Set.univ : Set V)) : Traceable G :=
  traceable_of_spanning_chain p.vertices p.ne_nil p.chain p.nodup
    (fun x => (p.mem_iff x).mpr (Set.mem_univ _))

/-- Any nonempty finite clique admits a spanning path. -/
noncomputable def ofClique [Fintype V] (hA : A.Nonempty)
    (hc : ∀ ⦃x y⦄, x ∈ A → y ∈ A → x ≠ y → G.Adj x y) : PathOn G A := by
  classical
  let s : Finset V := Finset.univ.filter (· ∈ A)
  have hm (x : V) : x ∈ s.toList ↔ x ∈ A := by simp [s]
  have hn : s.toList ≠ [] := by
    obtain ⟨x,hx⟩ := hA
    exact List.ne_nil_of_mem ((hm x).mpr hx)
  have hh : s.toList.Pairwise G.Adj := by
    have aux (l : List V) (hn : l.Nodup) (hs : ∀ x ∈ l, x ∈ A) :
        l.Pairwise G.Adj := by
      induction l with
      | nil => simp
      | cons v l ih =>
        rw [List.pairwise_cons]
        refine ⟨fun w hw => hc (hs v (by simp)) (hs w (by simp [hw])) ?_,
          ih (List.nodup_cons.mp hn).2 (fun z hz => hs z (by simp [hz]))⟩
        intro he
        exact (List.nodup_cons.mp hn).1 (he.symm ▸ hw)
    exact aux _ s.nodup_toList (fun x hx => (hm x).mp hx)
  exact ⟨s.toList,hn,hh.chain',s.nodup_toList,hm⟩

end PathOn

private theorem sets_of_two_lists {V : Type*} {G : SimpleGraph V}
    {S : Set V} {a b : List V} (ha : Good G a) (hb : Good G b)
    (hd : (a ++ b).Nodup) (hm : ∀ x, x ∈ a ++ b ↔ x ∈ S) :
    ∃ A B : Set V, Disjoint A B ∧ A ∪ B = S ∧
      Nonempty (PathOn G A) ∧ Nonempty (PathOn G B) := by
  obtain ⟨hna,hnb,hab⟩ := List.nodup_append.mp hd
  have hDis : Disjoint {v | v ∈ a} {v | v ∈ b} := Set.disjoint_left.mpr hab
  have hUnion : {v | v ∈ a} ∪ {v | v ∈ b} = S := by
    ext x
    simpa only [List.mem_append,Set.mem_union,Set.mem_setOf_eq] using hm x
  exact ⟨_,_,hDis,hUnion,⟨a,ha.1,ha.2,hna,fun _ => Iff.rfl⟩,
    ⟨b,hb.1,hb.2,hnb,fun _ => Iff.rfl⟩⟩

/-- If the region contains two distinct vertices, its cover can use exactly two nonempty paths. -/
theorem exact_two_path_cover {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hi : NoIndependentTriple G S) (hn : ∃ x ∈ S, ∃ y ∈ S, x ≠ y) :
    ∃ A B : Set V, Disjoint A B ∧ A ∪ B = S ∧
      Nonempty (PathOn G A) ∧ Nonempty (PathOn G B) := by
  obtain ⟨L,hLen,hGood,hDup,hMem⟩ := two_path_cover G S hi
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  cases L with
  | nil => exact (by simpa using (hMem x).mpr hx : False).elim
  | cons a L =>
    cases L with
    | nil =>
      have hA := hGood a (by simp)
      cases a with
      | nil => exact (hA.1 rfl).elim
      | cons u l =>
        cases l with
        | nil =>
          have hx' : x = u := by simpa using (hMem x).mpr hx
          have hy' : y = u := by simpa using (hMem y).mpr hy
          exact (hxy (hx'.trans hy'.symm)).elim
        | cons v l =>
          refine sets_of_two_lists (a := [u]) (b := v :: l) (by simp [Good])
            ⟨by simp,hA.2.tail⟩ ?_ ?_
          · simpa using hDup
          · simpa using hMem
    | cons b L =>
      have hzero : L = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hLen
        omega
      subst L
      exact sets_of_two_lists (hGood a (by simp)) (hGood b (by simp))
        (by simpa using hDup) (by simpa using hMem)

/-- A path cover of size at most two expressed as empty, one path or two paths. -/
theorem path_cover_cases {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hi : NoIndependentTriple G S) :
    S = ∅ ∨ Nonempty (PathOn G S) ∨
      ∃ A B : Set V, Disjoint A B ∧ A ∪ B = S ∧
        Nonempty (PathOn G A) ∧ Nonempty (PathOn G B) := by
  obtain ⟨L,hLen,hGood,hDup,hMem⟩ := two_path_cover G S hi
  cases L with
  | nil =>
    left
    ext x
    simpa using (hMem x).symm
  | cons a L =>
    right
    cases L with
    | nil =>
      exact Or.inl ⟨a,(hGood a (by simp)).1,(hGood a (by simp)).2,
        by simpa using hDup,by simpa using hMem⟩
    | cons b L =>
      have hzero : L = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hLen
        omega
      subst L
      exact Or.inr (sets_of_two_lists (hGood a (by simp)) (hGood b (by simp))
        (by simpa using hDup) (by simpa using hMem))

def CompleteBetween {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ B → G.Adj x y

namespace PathOn
variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- Both endpoints of a path may be used to attach an extra edge. -/
theorem orient_last (p : PathOn G A) {v : V}
    (h : G.Adj p.first v ∨ G.Adj p.last v) : ∃ q : PathOn G A, G.Adj q.last v := by
  rcases h with h | h
  · exact ⟨p.reverse,by simpa using h⟩
  · exact ⟨p,h⟩

theorem orient_first (p : PathOn G A) {v : V}
    (h : G.Adj v p.first ∨ G.Adj v p.last) : ∃ q : PathOn G A, G.Adj v q.first := by
  rcases h with h | h
  · exact ⟨p,h⟩
  · exact ⟨p.reverse,by simpa using h⟩

/-- Place a clique between two fixed endpoints. -/
theorem clique_between [Fintype V] (C : Set V) {a b : V}
    (hne : a ≠ b) (ha : a ∉ C) (hb : b ∉ C) (he : C = ∅ → G.Adj a b)
    (hc : ∀ ⦃x y⦄, x ∈ C → y ∈ C → x ≠ y → G.Adj x y)
    (heC : ∀ x ∈ C, G.Adj a x ∧ G.Adj x b) :
    ∃ p : PathOn G ({a,b} ∪ C), p.first = a ∧ p.last = b := by
  by_cases h : C.Nonempty
  · let q := ofClique h hc
    have hA : Disjoint ({a} : Set V) C := Set.disjoint_singleton_left.mpr ha
    let aq := (singleton a).join q hA (heC q.first q.first_mem).1
    have hB : Disjoint (({a} : Set V) ∪ C) {b} := by
      simp [hne,hne.symm,hb]
    let aqb := aq.join (singleton b) hB (by simpa [aq] using (heC q.last q.last_mem).2)
    have hSet : (({a} : Set V) ∪ C) ∪ {b} = {a,b} ∪ C := by
      ext x
      simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    exact ⟨aqb.cast hSet,by simp [aqb,aq],by simp [aqb]⟩
  · have hc0 : C = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hD : Disjoint ({a} : Set V) {b} := by simp [hne]
    let ab := (singleton a).join (singleton b) hD (he hc0)
    have hSet : ({a} : Set V) ∪ {b} = {a,b} ∪ C := by
      ext x
      simp [hc0,or_comm]
    exact ⟨ab.cast hSet,by simp [ab],by simp [ab]⟩

/-- Two paths, a path joining their endpoint sets, and up to two inserted paths
on the remaining vertices give a spanning path. -/
theorem assemble_two_rails [Fintype V] {M U : Set V}
    (p : PathOn G A) (q : PathOn G B) (r : PathOn G M)
    (hab : Disjoint A B) (ham : Disjoint A M) (hbm : Disjoint B M)
    (hau : Disjoint A U) (hbu : Disjoint B U) (hmu : Disjoint M U)
    (hpq : G.Adj p.last q.first) (hqr : G.Adj q.last r.first)
    (hU : NoIndependentTriple G U)
    (pU : ∀ x ∈ U, G.Adj p.first x ∨ G.Adj p.last x)
    (qU : ∀ x ∈ U, G.Adj x q.first ∨ G.Adj x q.last)
    (rU : ∀ x ∈ U, G.Adj r.first x ∧ G.Adj r.last x) :
    Nonempty (PathOn G (((A ∪ B) ∪ M) ∪ U)) := by
  let pq := p.join q hab hpq
  let pqr := pq.join r (Set.disjoint_union_left.mpr ⟨ham,hbm⟩) (by simpa [pq] using hqr)
  rcases path_cover_cases hU with h0 | h1 | h2
  · exact ⟨pqr.cast (by simp [h0])⟩
  · obtain ⟨u⟩ := h1
    have hu : Disjoint ((A ∪ B) ∪ M) U :=
      Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hau,hbu⟩,hmu⟩
    exact ⟨pqr.join u hu (by simpa [pqr] using (rU u.first u.first_mem).2)⟩
  · obtain ⟨F,H,hfh,hfu,⟨f⟩,⟨j⟩⟩ := h2
    have subF : F ⊆ U := fun _ hx => hfu ▸ Or.inl hx
    have subH : H ⊆ U := fun _ hx => hfu ▸ Or.inr hx
    obtain ⟨p',hpf⟩ := p.orient_last (pU f.first (subF f.first_mem))
    obtain ⟨q',hjq⟩ := q.orient_first (qU j.last (subH j.last_mem))
    let pf := p'.join f (hau.mono_right subF) hpf
    let pfr := pf.join r (Set.disjoint_union_left.mpr ⟨ham,hmu.symm.mono_left subF⟩)
      (by simpa [pf] using (rU f.last (subF f.last_mem)).1.symm)
    let pfrj := pfr.join j (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hau.mono_right subH,hfh⟩,hmu.mono_right subH⟩)
      (by simpa [pfr] using (rU j.first (subH j.first_mem)).2)
    let pfrjq := pfrj.join q' (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨hab,hbu.symm.mono_left subF⟩,hbm.symm⟩,
        hbu.symm.mono_left subH⟩) (by simpa [pfrj] using hjq)
    have hSet : (((A ∪ F) ∪ M) ∪ H) ∪ B = ((A ∪ B) ∪ M) ∪ U := by
      rw [← hfu]
      ext x
      simp only [Set.mem_union]
      tauto
    exact ⟨pfrjq.cast hSet⟩

end PathOn

#print axioms traceable_of_spanning_chain
#print axioms two_path_cover
#print axioms exact_two_path_cover
#print axioms PathOn.assemble_two_rails

namespace PathOn
variable {V : Type*} {G : SimpleGraph V}

/-- When the two selected claw leaves have no path between them within their own
region, use them separately, on either side of the far blocks and extra paths. -/
theorem assemble_separate_leaves [Fintype V] {C W U : Set V} {a b : V}
    (p : PathOn G C) (r : PathOn G W) (hab : a ≠ b)
    (hC : Disjoint ({a,b} : Set V) C) (hW : Disjoint ({a,b} : Set V) W)
    (hU : Disjoint ({a,b} : Set V) U) (hcw : Disjoint C W)
    (hcu : Disjoint C U) (hwu : Disjoint W U)
    (ha : G.Adj p.last a)
    (ar : G.Adj a r.first ∧ G.Adj a r.last) (br : G.Adj b r.first ∧ G.Adj b r.last)
    (uInd : NoIndependentTriple G U)
    (rU : ∀ x ∈ U, G.Adj r.first x ∧ G.Adj r.last x)
    (leaves : ∀ x ∈ U, G.Adj a x ∨ G.Adj b x)
    (split : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ¬ G.Adj x y →
      (G.Adj a x ∧ G.Adj b y) ∨ (G.Adj b x ∧ G.Adj a y)) :
    Nonempty (PathOn G (((C ∪ ({a,b} : Set V)) ∪ W) ∪ U)) := by
  have bridge : ∃ q : PathOn G (W ∪ U), G.Adj a q.first ∧ G.Adj b q.last := by
    by_cases hsingle : Nonempty (PathOn G U)
    · obtain ⟨u⟩ := hsingle
      let q := r.join u hwu (rU u.first u.first_mem).2
      rcases leaves u.last u.last_mem with h | h
      · exact ⟨q.reverse,by simpa [q] using h,by simpa [q] using br.1⟩
      · exact ⟨q,by simpa [q] using ar.1,by simpa [q] using h⟩
    · rcases path_cover_cases uInd with h0 | h1 | h2
      · exact ⟨r.cast (by simp [h0]),by simpa using ar.1,by simpa using br.2⟩
      · exact (hsingle h1).elim
      · obtain ⟨F,J,hfj,hunion,⟨f⟩,⟨j⟩⟩ := h2
        have hF : F ⊆ U := fun _ h => hunion ▸ Or.inl h
        have hJ : J ⊆ U := fun _ h => hunion ▸ Or.inr h
        have hn : ¬ G.Adj f.first j.last := by
          intro he
          have he' : G.Adj f.reverse.last j.reverse.first := by simpa using he
          exact hsingle ⟨(f.reverse.join j.reverse hfj he').cast hunion⟩
        let fr := f.join r (hwu.symm.mono_left hF) (rU f.last (hF f.last_mem)).1.symm
        let q := fr.join j (Set.disjoint_union_left.mpr ⟨hfj,hwu.mono_right hJ⟩)
          (by simpa [fr] using (rU j.first (hJ j.first_mem)).2)
        have hSet : (F ∪ W) ∪ J = W ∪ U := by
          rw [← hunion]
          ext x
          simp only [Set.mem_union]
          tauto
        have hne : f.first ≠ j.last := fun he =>
          Set.disjoint_left.mp hfj f.first_mem (he.symm ▸ j.last_mem)
        rcases split f.first (hF f.first_mem) j.last (hJ j.last_mem) hne hn with hs | hs
        · exact ⟨q.cast hSet,by simpa [q,fr] using hs.1,by simpa [q] using hs.2⟩
        · exact ⟨q.reverse.cast hSet,by simpa [q] using hs.2,by simpa [q,fr] using hs.1⟩
  obtain ⟨q,haq,hqb⟩ := bridge
  have sa : ({a} : Set V) ⊆ {a,b} := by simp
  have sb : ({b} : Set V) ⊆ {a,b} := by simp
  have dab : Disjoint ({a} : Set V) {b} := by simp [hab]
  let pa := p.join (singleton a) (hC.symm.mono_right sa) ha
  have hpa : Disjoint (C ∪ {a}) (W ∪ U) := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_right.mpr ⟨hcw,hcu⟩,
      Set.disjoint_union_right.mpr ⟨hW.mono_left sa,hU.mono_left sa⟩⟩
  let paq := pa.join q hpa (by simpa [pa] using haq)
  have hpaq : Disjoint ((C ∪ {a}) ∪ (W ∪ U)) {b} := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨hC.symm.mono_right sb,dab⟩,
      Set.disjoint_union_left.mpr ⟨hW.symm.mono_right sb,hU.symm.mono_right sb⟩⟩
  let paqb := paq.join (singleton b) hpaq (by simpa [paq] using hqb.symm)
  have hSet : ((C ∪ ({a} : Set V)) ∪ (W ∪ U)) ∪ {b} = ((C ∪ {a,b}) ∪ W) ∪ U := by
    ext x
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  exact ⟨paqb.cast hSet⟩
end PathOn

#print axioms PathOn.assemble_separate_leaves

/-- Assemble finitely many disjoint path blocks whose endpoint sets are
completely joined across distinct blocks. -/
theorem join_path_blocks {V ι : Type*} {G : SimpleGraph V}
    (R E : ι → Set V)
    (hp : ∀ i, ∃ p : PathOn G (R i), p.first ∈ E i ∧ p.last ∈ E i)
    (hd : ∀ i j, i ≠ j → Disjoint (R i) (R j))
    (he : ∀ i j, i ≠ j → CompleteBetween G (E i) (E j))
    (I : Finset ι) (hI : I.Nonempty) :
    ∃ p : PathOn G {x | ∃ i ∈ I, x ∈ R i},
      (∃ i ∈ I, p.first ∈ E i) ∧ (∃ i ∈ I, p.last ∈ E i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert i J hi ih =>
    obtain ⟨p,hf,hl⟩ := hp i
    by_cases hJ : J.Nonempty
    · obtain ⟨q,⟨j,hj,hqf⟩,⟨k,hk,hql⟩⟩ := ih hJ
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      have hDisj : Disjoint (R i) {x | ∃ j ∈ J, x ∈ R j} := by
        refine Set.disjoint_left.mpr fun x hx hz => ?_
        obtain ⟨j,hj,hz⟩ := hz
        exact Set.disjoint_left.mp (hd i j (fun h => hi (h.symm ▸ hj))) hx hz
      let pq := p.join q hDisj (he i j hij hl hqf)
      have hSet : R i ∪ {x | ∃ j ∈ J, x ∈ R j} = {x | ∃ j ∈ insert i J, x ∈ R j} := by
        ext x
        simp only [Set.mem_union,Set.mem_setOf_eq,Finset.mem_insert]
        constructor
        · rintro (h | ⟨j,hj,hr⟩)
          · exact ⟨i,Or.inl rfl,h⟩
          · exact ⟨j,Or.inr hj,hr⟩
        · rintro ⟨j,(rfl | hj),hr⟩
          · exact Or.inl hr
          · exact Or.inr ⟨j,hj,hr⟩
      exact ⟨pq.cast hSet,⟨i,by simp,by simpa [pq] using hf⟩,
        ⟨k,Finset.mem_insert_of_mem hk,by simpa [pq] using hql⟩⟩
    · have hEmpty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      have hSet : R i = {x | ∃ j ∈ insert i J, x ∈ R j} := by
        ext x
        simp [hEmpty]
      exact ⟨p.cast hSet,⟨i,by simp,by simpa using hf⟩,⟨i,by simp,by simpa using hl⟩⟩

#print axioms join_path_blocks

namespace PathOn
variable {V : Type*} {G : SimpleGraph V}

/-- Insert a cover by at most two paths on the two joins of an existing path. -/
theorem insert_on_two_joins [Fintype V] {A W B U : Set V}
    (p : PathOn G A) (r : PathOn G W) (q : PathOn G B)
    (dAW : Disjoint A W) (dAB : Disjoint A B) (dWB : Disjoint W B)
    (dAU : Disjoint A U) (dWU : Disjoint W U) (dBU : Disjoint B U)
    (epr : G.Adj p.last r.first) (erq : G.Adj r.last q.first)
    (hU : NoIndependentTriple G U)
    (pU : ∀ u ∈ U, G.Adj p.last u)
    (rU : ∀ u ∈ U, G.Adj r.first u ∧ G.Adj r.last u)
    (qU : ∀ u ∈ U, G.Adj u q.first) :
    Nonempty (PathOn G (((A ∪ W) ∪ B) ∪ U)) := by
  rcases path_cover_cases hU with h0 | h1 | h2
  · let pr := p.join r dAW epr
    let prq := pr.join q (Set.disjoint_union_left.mpr ⟨dAB,dWB⟩) (by simpa [pr] using erq)
    exact ⟨prq.cast (by simp [h0])⟩
  · obtain ⟨u⟩ := h1
    let pu := p.join u dAU (pU u.first u.first_mem)
    let pur := pu.join r (Set.disjoint_union_left.mpr ⟨dAW,dWU.symm⟩)
      (by simpa [pu] using (rU u.last u.last_mem).1.symm)
    let purq := pur.join q (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨dAB,dBU.symm⟩,dWB⟩) (by simpa [pur] using erq)
    have hSet : ((A ∪ U) ∪ W) ∪ B = ((A ∪ W) ∪ B) ∪ U := by
      ext x
      simp only [Set.mem_union]
      tauto
    exact ⟨purq.cast hSet⟩
  · obtain ⟨F,J,dfj,hu,⟨f⟩,⟨j⟩⟩ := h2
    have subF : F ⊆ U := fun _ hf => hu ▸ Or.inl hf
    have subJ : J ⊆ U := fun _ hj => hu ▸ Or.inr hj
    let pf := p.join f (dAU.mono_right subF) (pU f.first (subF f.first_mem))
    let pfr := pf.join r (Set.disjoint_union_left.mpr ⟨dAW,dWU.symm.mono_left subF⟩)
      (by simpa [pf] using (rU f.last (subF f.last_mem)).1.symm)
    let pfrj := pfr.join j (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨dAU.mono_right subJ,dfj⟩,dWU.mono_right subJ⟩)
      (by simpa [pfr] using (rU j.first (subJ j.first_mem)).2)
    let pfrjq := pfrj.join q (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨dAB,dBU.symm.mono_left subF⟩,dWB⟩,
        dBU.symm.mono_left subJ⟩) (by simpa [pfrj] using qU j.last (subJ j.last_mem))
    have hSet : (((A ∪ F) ∪ W) ∪ J) ∪ B = ((A ∪ W) ∪ B) ∪ U := by
      rw [← hu]
      ext x
      simp only [Set.mem_union]
      tauto
    exact ⟨pfrjq.cast hSet⟩

end PathOn

#print axioms PathOn.insert_on_two_joins

end Graffiti199K2


namespace Graffiti199K2
open SimpleGraph
open Set

variable {V : Type*} {G : SimpleGraph V} {Q : Fin 4 ↪ V}

/-- The far component containing the given far vertex. -/
def FarRegion (G : SimpleGraph V) (Q : Fin 4 ↪ V) (y : {v | Far G Q v}) : Set V :=
  {z | ∃ hz : Far G Q z, (FarGraph G Q).Reachable y ⟨z,hz⟩}

/-- Near vertices that are adjacent to the given far component. -/
def AttachmentRegion (G : SimpleGraph V) (Q : Fin 4 ↪ V) (y : {v | Far G Q v}) : Set V :=
  {x | Near G Q x ∧ G.Adj x y.val}

private theorem farRegion_self (y : {v | Far G Q v}) : y.val ∈ FarRegion G Q y :=
  ⟨y.property,Reachable.rfl⟩

private theorem attachment_far_disjoint (y z : {v | Far G Q v}) :
    Disjoint (AttachmentRegion G Q y) (FarRegion G Q z) := by
  refine Set.disjoint_left.mpr (fun x hx hz => ?_)
  obtain ⟨hxF,_⟩ := hz
  obtain ⟨i,hi⟩ := hx.1.2
  have hm : HasMask G Q x 0 := hxF.2
  have hfalse : ¬ (0 : ℕ).testBit i.val = true := by simp
  exact hfalse ((hm i).mp hi)

private theorem region_adjacency (h : NoTree5 G) (hq : IsClaw G Q)
    {y : {v | Far G Q v}} {x z : V}
    (hx : x ∈ AttachmentRegion G Q y) (hz : z ∈ FarRegion G Q y) : G.Adj x z := by
  obtain ⟨hzF,hr⟩ := hz
  exact (near_attachment_constant h hq hx.1 hr).mp hx.2

private theorem region_clique (h : NoTree5 G) (hq : IsClaw G Q) (hc : G.Connected)
    {y : {v | Far G Q v}} {x z : V}
    (hx : x ∈ FarRegion G Q y) (hz : z ∈ FarRegion G Q y) (hne : x ≠ z) : G.Adj x z := by
  obtain ⟨hxF,hrx⟩ := hx
  obtain ⟨hzF,hrz⟩ := hz
  exact far_component_clique h hq hc (hrx.symm.trans hrz)
    (fun he => hne (congrArg Subtype.val he))

private theorem mask_spare_leaf : ∀ m : Mask, AttachmentMask m →
    m.val.testBit 0 = true ∧ ∃ i : Fin 4, i ≠ 0 ∧ m.val.testBit i.val = false := by
  decide

private theorem claw_center_adj (hq : IsClaw G Q) {i : Fin 4} (hi : i ≠ 0) :
    G.Adj (Q 0) (Q i) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact (hq 0 1).mpr rfl
  · exact (hq 0 2).mpr rfl
  · exact (hq 0 3).mpr rfl

theorem attachmentRegion_no_independent_triple (h : NoTree5 G) (hq : IsClaw G Q)
    (y : {v | Far G Q v}) : NoIndependentTriple G (AttachmentRegion G Q y) := by
  classical
  intro a b d ha hb hd hab had hbd
  by_contra! hn
  obtain ⟨nab,nad,nbd⟩ := hn
  obtain ⟨m,hm⟩ := mask_exists G Q a
  obtain ⟨n,hn⟩ := mask_exists G Q b
  obtain ⟨s,hs⟩ := mask_exists G Q d
  have hmn : m = n := by
    by_contra hne
    exact nab (same_component_distinct_masks_adjacent h hq ha.1 hb.1 y.property ha.2 hb.2 hm hn hne hab)
  have hms : m = s := by
    by_contra hne
    exact nad (same_component_distinct_masks_adjacent h hq ha.1 hd.1 y.property ha.2 hd.2 hm hs hne had)
  subst n
  subst s
  obtain ⟨hc,i,hi,hnone⟩ := mask_spare_leaf m (near_far_attachment_mask h hq ha.1 y.property ha.2 hm)
  exact no_four_independent_neighbors h ((hm 0).mpr hc) ((hn 0).mpr hc) ((hs 0).mpr hc)
    (claw_center_adj hq hi) hab had (ha.1.1 i) hbd (hb.1.1 i) (hd.1.1 i) nab nad
    (fun he => Bool.false_ne_true (hnone.symm.trans ((hm i).mp he.symm))) nbd
    (fun he => Bool.false_ne_true (hnone.symm.trans ((hn i).mp he.symm)))
    (fun he => Bool.false_ne_true (hnone.symm.trans ((hs i).mp he.symm)))

/-- Vertices complete to an attachment but with no edges to its far representative
can be covered by at most two paths. -/
theorem no_independent_triple_beside_attachment (h : NoTree5 G) {x y : V}
    (hxy : G.Adj x y) {S : Set V} (hy : y ∉ S) (ht : ∀ v ∈ S, G.Adj x v ∧ ¬ G.Adj y v) :
    NoIndependentTriple G S := by
  classical
  intro a b d ha hb hd hab had hbd
  by_contra! hn
  obtain ⟨nab,nad,nbd⟩ := hn
  obtain ⟨hxa,hya⟩ := ht a ha
  obtain ⟨hxb,hyb⟩ := ht b hb
  obtain ⟨hxd,hyd⟩ := ht d hd
  exact no_four_independent_neighbors h hxa hxb hxd hxy hab had
    (fun he => hy (he ▸ ha)) hbd
    (fun he => hy (he ▸ hb)) (fun he => hy (he ▸ hd))
    nab nad (fun he => hya he.symm) nbd (fun he => hyb he.symm) (fun he => hyd he.symm)

/-- A far component and its attachments have a spanning path whose endpoints are attachments. -/
theorem far_component_path_block [Fintype V] (h : NoTree5 G) (hq : IsClaw G Q)
    (hc : G.Connected) (hk : ConnectivityAtLeast G 2) (y : {v | Far G Q v}) :
    ∃ p : PathOn G (AttachmentRegion G Q y ∪ FarRegion G Q y),
      p.first ∈ AttachmentRegion G Q y ∧ p.last ∈ AttachmentRegion G Q y := by
  classical
  let S := AttachmentRegion G Q y
  let M := FarRegion G Q y
  obtain ⟨x,w,hne,hx,hw,hxy,hwy⟩ := far_has_two_attachments h hq hc hk y
  have htwo : ∃ x ∈ S, ∃ w ∈ S, x ≠ w := ⟨x,⟨hx,hxy⟩,w,⟨hw,hwy⟩,hne⟩
  obtain ⟨A,B,hab,hu,⟨p⟩,⟨q⟩⟩ :=
    exact_two_path_cover (attachmentRegion_no_independent_triple h hq y) htwo
  change A ∪ B = S at hu
  have ha : A ⊆ S := fun _ hx => hu ▸ Or.inl hx
  have hb : B ⊆ S := fun _ hx => hu ▸ Or.inr hx
  let m : PathOn G M := PathOn.ofClique ⟨y.val,farRegion_self y⟩
    (fun ⦃_ _⦄ hx hz hne => region_clique h hq hc hx hz hne)
  have hm := attachment_far_disjoint (G := G) (Q := Q) y y
  let pm := p.join m (hm.mono_left ha) (region_adjacency h hq (ha p.last_mem) m.first_mem)
  have hpm : Disjoint (A ∪ M) B := Set.disjoint_union_left.mpr
    ⟨hab,hm.symm.mono_right hb⟩
  have he : G.Adj pm.last q.first := by
    simpa [pm] using (region_adjacency h hq (hb q.first_mem) m.last_mem).symm
  have hSet : (A ∪ M) ∪ B = S ∪ M := by
    rw [← hu]
    ext x
    simp only [Set.mem_union]
    tauto
  exact ⟨((pm.join q hpm he).cast hSet),by simpa [pm] using ha p.first_mem,
    by simpa using hb q.last_mem⟩

#print axioms no_independent_triple_beside_attachment
#print axioms far_component_path_block


/-- Near vertices that have a far neighbor. -/
def Attached (G : SimpleGraph V) (Q : Fin 4 ↪ V) (v : V) : Prop :=
  Near G Q v ∧ ∃ y : {w | Far G Q w}, G.Adj v y.val

/-- Far vertices with all their near attachments. -/
def AllFarBlocks (G : SimpleGraph V) (Q : Fin 4 ↪ V) : Set V :=
  {v | Attached G Q v ∨ Far G Q v}

/-- The union of the far components with their attachment sets is covered by one path
with endpoints in the attachment sets. -/
theorem all_far_blocks_path [Fintype V] (h : NoTree5 G) (hq : IsClaw G Q)
    (hc : G.Connected) (hk : ConnectivityAtLeast G 2) (y : {v | Far G Q v}) :
    ∃ p : PathOn G (AllFarBlocks G Q), Attached G Q p.first ∧ Attached G Q p.last := by
  classical
  let H := FarGraph G Q
  let C := H.ConnectedComponent
  have surj : Function.Surjective H.connectedComponentMk := Quot.mk_surjective
  letI : Fintype C := Fintype.ofSurjective H.connectedComponentMk surj
  let rep (i : C) := Classical.choose (surj i)
  have hrep (i : C) : H.connectedComponentMk (rep i) = i := Classical.choose_spec (surj i)
  let A (i : C) := AttachmentRegion G Q (rep i)
  let M (i : C) := FarRegion G Q (rep i)
  let R (i : C) := A i ∪ M i
  have cross (i j : C) (hne : i ≠ j) : ¬ H.Reachable (rep i) (rep j) := by
    intro hr
    have eq : H.connectedComponentMk (rep i) = H.connectedComponentMk (rep j) :=
      SimpleGraph.ConnectedComponent.sound hr
    exact hne ((hrep i).symm.trans (eq.trans (hrep j)))
  have hd (i j : C) (hne : i ≠ j) : Disjoint (R i) (R j) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · have hr : (rep i).val ≠ (rep j).val := fun he => cross i j hne
        (Subtype.ext he ▸ Reachable.rfl)
      have he : G.Adj (rep i).val (rep j).val :=
        far_neighbors_adjacent h hq hv.1 (rep i).property (rep j).property hv.2 hw.2 hr
      exact cross i j hne ⟨.cons he .nil⟩
    · exact Set.disjoint_left.mp (attachment_far_disjoint (rep i) (rep j)) hv hw
    · exact Set.disjoint_left.mp (attachment_far_disjoint (rep j) (rep i)) hw hv
    · obtain ⟨_,hri⟩ := hv
      obtain ⟨_,hrj⟩ := hw
      exact cross i j hne (hri.trans hrj.symm)
  have he (i j : C) (hne : i ≠ j) : CompleteBetween G (A i) (A j) := by
    intro x v hx hv
    obtain ⟨m,hm⟩ := mask_exists G Q x
    obtain ⟨n,hn⟩ := mask_exists G Q v
    exact (attachments_of_distinct_far_components h hq (cross i j hne)
      hx.1 hv.1 hx.2 hv.2 hm hn).2
  obtain ⟨p,⟨i,_,hfi⟩,⟨j,_,hlj⟩⟩ :=
    join_path_blocks R A (fun i => far_component_path_block h hq hc hk (rep i)) hd he
      (Finset.univ : Finset C) ⟨H.connectedComponentMk y,Finset.mem_univ _⟩
  have hSet : {v | ∃ i ∈ (Finset.univ : Finset C), v ∈ R i} = AllFarBlocks G Q := by
    ext v
    constructor
    · rintro ⟨i,_,hi⟩
      rcases hi with hi | ⟨hi,_⟩
      · exact Or.inl ⟨hi.1,rep i,hi.2⟩
      · exact Or.inr hi
    · intro hv
      rcases hv with ⟨hN,z,hz⟩ | hv
      · let i := H.connectedComponentMk z
        have hr : H.Reachable (rep i) z := SimpleGraph.ConnectedComponent.exact (hrep i)
        exact ⟨i,Finset.mem_univ _,Or.inl ⟨hN,(near_attachment_constant h hq hN hr).mpr hz⟩⟩
      · let z : {w | Far G Q w} := ⟨v,hv⟩
        let i := H.connectedComponentMk z
        have hr : H.Reachable (rep i) z := SimpleGraph.ConnectedComponent.exact (hrep i)
        exact ⟨i,Finset.mem_univ _,Or.inr ⟨hv,hr⟩⟩
  exact ⟨p.cast hSet,⟨hfi.1,rep i,hfi.2⟩,⟨hlj.1,rep j,hlj.2⟩⟩

#print axioms all_far_blocks_path

private def UniformExtra (m : Mask) : Prop := m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 14 ∨ m = 15

private instance (m : Mask) : Decidable (UniformExtra m) := by
  unfold UniformExtra
  infer_instance

private theorem uniform_extra_contacts :
    ∀ m : Mask, UniformExtra m →
      ((m.val.testBit 0 = true ∨ m.val.testBit 3 = true) ∧
        (m.val.testBit 1 = true ∨ m.val.testBit 2 = true)) := by decide

private theorem distinct_leaf_contacts : ∀ m n : Mask, UniformExtra m → UniformExtra n →
    (m.val.testBit 1 = true ∧ n.val.testBit 2 = true) ∨
    (m.val.testBit 2 = true ∧ n.val.testBit 1 = true) ∨
    (m = 3 ∧ n = 3) ∨ (m = 5 ∧ n = 5) := by
  intro m
  fin_cases m <;> decide

private theorem near_not_far {x : V} (hn : Near G Q x) (hf : Far G Q x) : False := by
  obtain ⟨i,hi⟩ := hn.2
  have hz := (hf.2 i).mp hi
  simp at hz

private theorem outside_near_or_far {x : V} (ho : Outside Q x) : Near G Q x ∨ Far G Q x := by
  classical
  by_cases h : ∃ i, G.Adj (Q i) x
  · exact Or.inl ⟨ho,h⟩
  · exact Or.inr ⟨ho,fun i => iff_of_false (fun he => h ⟨i,he⟩) (by simp)⟩

private theorem disjoint_core_pair {i j : Fin 4} {W : Set V}
    (h : ∀ x ∈ W, Outside Q x) :
    Disjoint ({Q i,Q j} : Set V) W := by
  apply Set.disjoint_left.mpr
  intro x hx hw
  rcases (show x = Q i ∨ x = Q j by simpa using hx) with he | he
  · exact h x hw i he
  · exact h x hw j he

/-- If all attachments have the same specified mask, the graph is traceable. -/
theorem uniform_attachment_traceable [Fintype V] (h : NoTree5 G) (hq : IsClaw G Q)
    (hc : G.Connected) (hk : ConnectivityAtLeast G 2) (y : {v | Far G Q v})
    (hMask : ∀ x, Attached G Q x → HasMask G Q x 7) : Traceable G := by
  classical
  let W := AllFarBlocks G Q
  let N : Set V := {v | Near G Q v ∧ ¬ ∃ z : {w | Far G Q w}, G.Adj v z.val}
  let Y (m : Mask) : Set V := {v | v ∈ N ∧ HasMask G Q v m}
  let C : Set V := {Q 3,Q 0}
  let D : Set V := {Q 1,Q 2}
  let C' := C ∪ Y 9
  let D' := D ∪ Y 6
  let U : Set V := {v | v ∈ N ∧ ∃ m, HasMask G Q v m ∧ UniformExtra m}
  have dC : Disjoint C N := disjoint_core_pair fun _ hx => hx.1.1
  have dD : Disjoint D N := disjoint_core_pair fun _ hx => hx.1.1
  have wOutside (v : V) (hv : v ∈ W) : Outside Q v := by
    rcases hv with hs | hf
    · exact hs.1.1
    · exact hf.1
  have dCW : Disjoint C W := disjoint_core_pair wOutside
  have dDW : Disjoint D W := disjoint_core_pair wOutside
  have dNW : Disjoint N W := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases hw with hs | hf
    · exact hv.2 hs.2
    · exact near_not_far hv.1 hf
  have dCD : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro v hC hD
    rcases (show v = Q 3 ∨ v = Q 0 by simpa [C] using hC) with rfl | rfl <;>
      simp [D,Q.injective.eq_iff] at hD
  have ySub (m : Mask) : Y m ⊆ N := fun _ hx => hx.1
  have uSub : U ⊆ N := fun _ hx => hx.1
  have dY : Disjoint (Y 9) (Y 6) :=
    Set.disjoint_left.mpr (fun _ hx hy => (by decide : (9 : Mask) ≠ 6) (hx.2.unique hy.2))
  have dYU (m : Mask) (hm : ¬ UniformExtra m) : Disjoint (Y m) U := by
    apply Set.disjoint_left.mpr
    intro v hv hu
    obtain ⟨n,hn,hE⟩ := hu.2
    exact hm ((hn.unique hv.2) ▸ hE)
  have dC'D' : Disjoint C' D' := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_right.mpr ⟨dCD,dC.mono_right (ySub 6)⟩,
      Set.disjoint_union_right.mpr ⟨dD.symm.mono_left (ySub 9),dY⟩⟩
  have dC'W : Disjoint C' W := Set.disjoint_union_left.mpr ⟨dCW,dNW.mono_left (ySub 9)⟩
  have dD'W : Disjoint D' W := Set.disjoint_union_left.mpr ⟨dDW,dNW.mono_left (ySub 6)⟩
  have dC'U : Disjoint C' U := Set.disjoint_union_left.mpr ⟨dC.mono_right uSub,dYU 9 (by decide)⟩
  have dD'U : Disjoint D' U := Set.disjoint_union_left.mpr ⟨dD.mono_right uSub,dYU 6 (by decide)⟩
  obtain ⟨w,hs,hw⟩ := far_has_attachment h hq hc y
  have hws : Attached G Q w := ⟨hs,y,hw⟩
  have outside (x : V) (hx : x ∈ N) : x ∈ Y 6 ∨ x ∈ Y 9 ∨ x ∈ U := by
    obtain ⟨b,hb⟩ := mask_exists G Q x
    rcases attachment_outside_pattern h hq hs hx.1 y.property (hMask w hws) hw (fun he => hx.2 ⟨y,he⟩) hb with
      ⟨hm,_⟩ | ⟨hm,_⟩
    · rcases hm with rfl | rfl
      · exact Or.inl ⟨hx,hb⟩
      · exact Or.inr (Or.inl ⟨hx,hb⟩)
    · exact Or.inr (Or.inr ⟨hx,b,hb,hm⟩)
  have wU (x : V) (hx : Attached G Q x) (v : V) (hv : v ∈ U) : G.Adj x v := by
    obtain ⟨m,hm,hE⟩ := hv.2
    obtain ⟨z,hxz⟩ := hx.2
    rcases attachment_outside_pattern h hq hx.1 hv.1.1 z.property (hMask x hx) hxz
      (fun he => hv.1.2 ⟨z,he⟩) hm with
      ⟨hm',_⟩ | ⟨_,ha⟩
    · rcases hm' with rfl | rfl
      · exact ((by decide : ¬ UniformExtra 6) hE).elim
      · exact ((by decide : ¬ UniformExtra 9) hE).elim
    · exact ha
  have uIndependent : NoIndependentTriple G U :=
    no_independent_triple_beside_attachment h hw (fun hv => near_not_far hv.1.1 y.property)
      (fun v hv => ⟨wU w hws v hv,fun he => hv.1.2 ⟨y,he.symm⟩⟩)
  have hClique (m : Mask) (hm : CliqueMask m) :
      ∀ ⦃a b⦄, a ∈ Y m → b ∈ Y m → a ≠ b → G.Adj a b :=
    fun ⦃_ _⦄ ha hb hne => clique_mask_pair_adjacent h hq ha.1.1.1 hb.1.1.1 hne hm ha.2 hb.2
  obtain ⟨p,hp3,hp0⟩ : ∃ p : PathOn G C', p.first = Q 3 ∧ p.last = Q 0 :=
    PathOn.clique_between (Y 9) (Q.injective.ne (by decide))
      (fun hx => Set.disjoint_left.mp dC (by simp [C]) hx.1)
      (fun hx => Set.disjoint_left.mp dC (by simp [C]) hx.1)
      (fun _ => (claw_center_adj hq (by decide : (3 : Fin 4) ≠ 0)).symm) (hClique 9 (by decide))
      (fun _ hv => ⟨(hv.2 3).mpr rfl,((hv.2 0).mpr rfl).symm⟩)
  obtain ⟨r,hrf,hrl⟩ := all_far_blocks_path h hq hc hk y
  have pU (v : V) (hv : v ∈ U) : G.Adj p.first v ∨ G.Adj p.last v := by
    rw [hp3,hp0]
    obtain ⟨m,hm,he⟩ := hv.2
    rcases (uniform_extra_contacts m he).1 with h0 | h3
    · exact Or.inr ((hm 0).mpr h0)
    · exact Or.inl ((hm 3).mpr h3)
  have rU (v : V) (hv : v ∈ U) : G.Adj r.first v ∧ G.Adj r.last v :=
    ⟨wU _ hrf v hv,wU _ hrl v hv⟩
  have path_exists : Nonempty (PathOn G (((C' ∪ D') ∪ W) ∪ U)) := by
    by_cases hLeaf : (Y 6).Nonempty
    · obtain ⟨q,hq1,hq2⟩ : ∃ q : PathOn G D', q.first = Q 1 ∧ q.last = Q 2 :=
        PathOn.clique_between (Y 6) (Q.injective.ne (by decide))
          (fun hx => Set.disjoint_left.mp dD (by simp [D]) hx.1)
          (fun hx => Set.disjoint_left.mp dD (by simp [D]) hx.1)
          (fun he => (Set.not_nonempty_iff_eq_empty.mpr he hLeaf).elim) (hClique 6 (by decide))
          (fun _ hv => ⟨(hv.2 1).mpr rfl,((hv.2 2).mpr rfl).symm⟩)
      have qU (v : V) (hv : v ∈ U) : G.Adj v q.first ∨ G.Adj v q.last := by
        rw [hq1,hq2]
        obtain ⟨m,hm,he⟩ := hv.2
        exact ((uniform_extra_contacts m he).2).imp (fun h => ((hm 1).mpr h).symm)
          (fun h => ((hm 2).mpr h).symm)
      have hpq : G.Adj p.last q.first := by
        rw [hp0,hq1]
        exact claw_center_adj hq (by decide : (1 : Fin 4) ≠ 0)
      have hqr : G.Adj q.last r.first := by rw [hq2]; exact (hMask _ hrf 2).mpr rfl
      exact PathOn.assemble_two_rails p q r dC'D' dC'W dD'W dC'U dD'U
        (dNW.symm.mono_right uSub) hpq hqr uIndependent pU qU rU
    · have h0 : Y 6 = ∅ := Set.not_nonempty_iff_eq_empty.mp hLeaf
      have hs : D' = D := by simp [D',h0]
      have dDC' : Disjoint D C' := Set.disjoint_union_right.mpr ⟨dCD.symm,dD.mono_right (ySub 9)⟩
      have hp1 : G.Adj p.last (Q 1) := by rw [hp0]; exact claw_center_adj hq (by decide)
      have hr1 : G.Adj (Q 1) r.first ∧ G.Adj (Q 1) r.last :=
        ⟨(hMask _ hrf 1).mpr rfl,(hMask _ hrl 1).mpr rfl⟩
      have hr2 : G.Adj (Q 2) r.first ∧ G.Adj (Q 2) r.last :=
        ⟨(hMask _ hrf 2).mpr rfl,(hMask _ hrl 2).mpr rfl⟩
      have hContact (x : V) (hx : x ∈ U) : G.Adj (Q 1) x ∨ G.Adj (Q 2) x := by
        obtain ⟨m,hm,he⟩ := hx.2
        exact ((uniform_extra_contacts m he).2).imp (hm 1).mpr (hm 2).mpr
      have hSplit (x : V) (hx : x ∈ U) (z : V) (hz : z ∈ U) (hne : x ≠ z) (hn : ¬ G.Adj x z) :
          (G.Adj (Q 1) x ∧ G.Adj (Q 2) z) ∨ (G.Adj (Q 2) x ∧ G.Adj (Q 1) z) := by
        obtain ⟨m,hm,hme⟩ := hx.2
        obtain ⟨n,hn',hne'⟩ := hz.2
        rcases distinct_leaf_contacts m n hme hne' with hA | hB | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl ⟨(hm 1).mpr hA.1,(hn' 2).mpr hA.2⟩
        · exact Or.inr ⟨(hm 2).mpr hB.1,(hn' 1).mpr hB.2⟩
        · exact (hn (clique_mask_pair_adjacent h hq hx.1.1.1 hz.1.1.1 hne (by decide) hm hn')).elim
        · exact (hn (clique_mask_pair_adjacent h hq hx.1.1.1 hz.1.1.1 hne (by decide) hm hn')).elim
      have h := PathOn.assemble_separate_leaves p r (Q.injective.ne (by decide))
        dDC' dDW (dD.mono_right uSub) dC'W dC'U (dNW.symm.mono_right uSub)
        hp1 hr1 hr2 uIndependent rU hContact hSplit
      simpa only [hs] using h
  obtain ⟨path⟩ := path_exists
  have hall : ((C' ∪ D') ∪ W) ∪ U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases ho : Outside Q x
    · rcases outside_near_or_far ho with hn | hf
      · by_cases ha : ∃ z : {w | Far G Q w}, G.Adj x z.val
        · exact Or.inl (Or.inr (Or.inl ⟨hn,ha⟩))
        · rcases outside x ⟨hn,ha⟩ with hb | hc' | hu
          · exact Or.inl (Or.inl (Or.inr (Or.inr hb)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr hc')))
          · exact Or.inr hu
      · exact Or.inl (Or.inr (Or.inr hf))
    · unfold Outside at ho
      push_neg at ho
      obtain ⟨i,rfl⟩ := ho
      fin_cases i <;> simp [C',D',C,D]
  exact (path.cast hall).traceable

#print axioms uniform_attachment_traceable

private def branchLeaf (i : Fin 3) : Fin 4 := i.succ
private def branchMask (i : Fin 3) : Mask := ![3,5,9] i

private theorem branchLeaf_ne_zero (i : Fin 3) : branchLeaf i ≠ 0 := by
  fin_cases i <;> decide

private theorem branchLeaf_injective : Function.Injective branchLeaf := by
  intro a b h
  exact Fin.succ_injective _ h

private theorem branchMask_injective : Function.Injective branchMask := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | contradiction

private theorem branchMask_bits (i : Fin 3) :
    CenterLeafMask (branchMask i) ∧ CliqueMask (branchMask i) ∧
      (branchMask i).val.testBit 0 = true ∧ (branchMask i).val.testBit (branchLeaf i).val = true := by
  fin_cases i <;> decide

private theorem fullLeaves_bits (m : Mask) (h : FullLeavesMask m) (i : Fin 3) :
    m.val.testBit (branchLeaf i).val = true := by
  rcases h with rfl | rfl <;> fin_cases i <;> decide

private theorem mixed_distinct_contacts :
    ∀ a b : Mask, AttachmentMask a → AttachmentMask b → ∃ i j k : Fin 3,
      i ≠ j ∧ k ≠ i ∧ k ≠ j ∧
      a.val.testBit (branchLeaf i).val = true ∧ b.val.testBit (branchLeaf j).val = true ∧
      ∀ s : Fin 3, s = i ∨ s = j ∨ s = k := by
  intro a
  fin_cases a <;> decide

/-- A nondominating claw whose attachments realize masks 7 and 11 gives a spanning path. -/
theorem mixed_attachment_traceable [Fintype V] (h : NoTree5 G) (hq : IsClaw G Q)
    (hc : G.Connected) (hk : ConnectivityAtLeast G 2)
    (hmix : ∃ x, Attached G Q x ∧ HasMask G Q x 7)
    (hmix' : ∃ x, Attached G Q x ∧ HasMask G Q x 11) : Traceable G := by
  classical
  obtain ⟨a,⟨an,y,ay⟩,am⟩ := hmix
  obtain ⟨b,⟨bn,z,bz⟩,bm⟩ := hmix'
  have by' : G.Adj b y.val := by
    by_cases hr : (FarGraph G Q).Reachable y z
    · exact (near_attachment_constant h hq bn hr).mpr bz
    · exact ((by decide : (7 : Mask) ≠ 11)
        (attachments_of_distinct_far_components h hq hr an bn ay bz am bm).1).elim
  let W := AllFarBlocks G Q
  let N : Set V := {v | Near G Q v ∧ ¬ ∃ z : {w | Far G Q w}, G.Adj v z.val}
  let Y (i : Fin 3) : Set V := {v | v ∈ N ∧ HasMask G Q v (branchMask i)}
  let B (i : Fin 3) := insert (Q (branchLeaf i)) (Y i)
  let C : Set V := {Q 0}
  let U : Set V := {v | v ∈ N ∧ ∃ m, HasMask G Q v m ∧ FullLeavesMask m}
  have noFar (x : V) (hx : x ∈ N) (z : {w | Far G Q w}) : ¬ G.Adj x z.val :=
    fun he => hx.2 ⟨z,he⟩
  have outside (x : V) (hx : x ∈ N) : (∃ i, x ∈ Y i) ∨ x ∈ U := by
    obtain ⟨b',hb'⟩ := mask_exists G Q x
    rcases mixed_attachment_outside_pattern h hq an bn hx.1 y.property am bm ay by'
      (noFar x hx y) hb' with ⟨hm,_,_⟩ | ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩
    · rcases hm with rfl | rfl | rfl
      · exact Or.inl ⟨0,hx,hb'⟩
      · exact Or.inr ⟨hx,14,hb',Or.inl rfl⟩
      · exact Or.inr ⟨hx,15,hb',Or.inr rfl⟩
    · exact Or.inl ⟨1,hx,hb'⟩
    · exact Or.inl ⟨2,hx,hb'⟩
  have nW : Disjoint N W := by
    apply Set.disjoint_left.mpr
    intro x hx hw
    rcases hw with ha | hf
    · exact hx.2 ha.2
    · exact near_not_far hx.1 hf
  have wO (x : V) (hx : x ∈ W) : Outside Q x := by
    rcases hx with ha | hf
    · exact ha.1.1
    · exact hf.1
  have nO (x : V) (hx : x ∈ N) : Outside Q x := hx.1.1
  have bW (i : Fin 3) : Disjoint (B i) W := by
    apply Set.disjoint_left.mpr
    intro x hx hw
    rcases Set.mem_insert_iff.mp hx with he | hy
    · exact wO x hw _ he
    · exact Set.disjoint_left.mp nW hy.1 hw
  have bC (i : Fin 3) : Disjoint (B i) C := by
    apply Set.disjoint_left.mpr
    intro x hx hc'
    have hx0 : x = Q 0 := hc'
    rcases Set.mem_insert_iff.mp hx with he | hy
    · exact branchLeaf_ne_zero i (Q.injective (he.symm.trans hx0))
    · exact nO x hy.1 0 hx0
  have bB (i j : Fin 3) (hne : i ≠ j) : Disjoint (B i) (B j) := by
    apply Set.disjoint_left.mpr
    intro x hi hj
    rcases Set.mem_insert_iff.mp hi with hi | hi <;> rcases Set.mem_insert_iff.mp hj with hj | hj
    · exact hne (branchLeaf_injective (Q.injective (hi.symm.trans hj)))
    · exact nO x hj.1 _ hi
    · exact nO x hi.1 _ hj
    · exact hne (branchMask_injective (hi.2.unique hj.2))
  have bU (i : Fin 3) : Disjoint (B i) U := by
    apply Set.disjoint_left.mpr
    intro x hx hu
    rcases Set.mem_insert_iff.mp hx with he | hy
    · exact nO x hu.1 _ he
    · obtain ⟨m,hm,hf⟩ := hu.2
      have he := hy.2.unique hm
      have hn : ¬ FullLeavesMask (branchMask i) := by fin_cases i <;> decide
      exact hn (he.symm ▸ hf)
  have cU : Disjoint C U :=
    Set.disjoint_left.mpr (fun x hx hu => nO x hu.1 0 hx)
  have cW : Disjoint C W :=
    Set.disjoint_left.mpr (fun x hx hw => wO x hw 0 hx)
  have wU : Disjoint W U := nW.symm.mono_right (fun _ hx => hx.1)
  have centerB (i : Fin 3) (x : V) (hx : x ∈ B i) : G.Adj (Q 0) x := by
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact claw_center_adj hq (branchLeaf_ne_zero i)
    · exact (hx.2 0).mpr (branchMask_bits i).2.2.1
  have bClique (i : Fin 3) : ∀ ⦃x v⦄, x ∈ B i → v ∈ B i → x ≠ v → G.Adj x v := by
    intro x v hx hv hne
    rcases Set.mem_insert_iff.mp hx with rfl | hx <;> rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact (hne rfl).elim
    · exact (hv.2 (branchLeaf i)).mpr (branchMask_bits i).2.2.2
    · exact ((hx.2 (branchLeaf i)).mpr (branchMask_bits i).2.2.2).symm
    · exact clique_mask_pair_adjacent h hq (nO x hx.1) (nO v hv.1) hne
        (branchMask_bits i).2.1 hx.2 hv.2
  let p (i : Fin 3) : PathOn G (B i) :=
    PathOn.ofClique ⟨_,Set.mem_insert _ _⟩ (bClique i)
  have attU (x : V) (hx : Attached G Q x) (u : V) (hu : u ∈ U) : G.Adj x u := by
    obtain ⟨f,hxf⟩ := hx.2
    obtain ⟨m,hm⟩ := mask_exists G Q x
    obtain ⟨n,hn,hnf⟩ := hu.2
    exact (extra_attachment_adjacency h hq hx.1 hu.1.1 f.property hxf
      (noFar u hu.1 f) hm hn).1 hnf
  have attB (x : V) (hx : Attached G Q x) (i : Fin 3) {m : Mask} (hm : HasMask G Q x m)
      (hb : m.val.testBit (branchLeaf i).val = true) (v : V) (hv : v ∈ B i) : G.Adj x v := by
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact ((hm _).mpr hb).symm
    · obtain ⟨f,hxf⟩ := hx.2
      exact ((extra_attachment_adjacency h hq hx.1 hv.1.1 f.property hxf (noFar v hv.1 f) hm hv.2).2
        _ (branchLeaf_ne_zero i) (branchMask_bits i).1 (branchMask_bits i).2.2.2).mpr hb
  have extraB (i : Fin 3) (x : V) (hx : x ∈ B i) (u : V) (hu : u ∈ U) : G.Adj x u := by
    obtain ⟨m,hm,hf⟩ := hu.2
    have hne : x ≠ u := fun he => Set.disjoint_left.mp (bU i) hx (he.symm ▸ hu)
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (hm _).mpr (fullLeaves_bits m hf i)
    · exact center_leaf_full_leaves_adjacent h hq (nO x hx.1) (nO u hu.1) hne
        (branchMask_bits i).1 hf hx.2 hm
  have uInd : NoIndependentTriple G U :=
    no_independent_triple_beside_attachment h ay (fun hu => near_not_far hu.1.1 y.property)
      (fun u hu => ⟨attU a ⟨an,y,ay⟩ u hu,fun he => noFar u hu.1 y he.symm⟩)
  obtain ⟨r,hrf,hrl⟩ := all_far_blocks_path h hq hc hk y
  obtain ⟨m,hm⟩ := mask_exists G Q r.first
  obtain ⟨n,hn⟩ := mask_exists G Q r.last
  have isAtt (v : V) (hv : Attached G Q v) (s : Mask) (hs : HasMask G Q v s) :
      AttachmentMask s := by
    obtain ⟨f,hvf⟩ := hv.2
    exact near_far_attachment_mask h hq hv.1 f.property hvf hs
  obtain ⟨i,j,k,hij,hki,hkj,hmi,hnj,hAll⟩ :=
    mixed_distinct_contacts m n (isAtt _ hrf m hm) (isAtt _ hrl n hn)
  let pc := (p k).join (PathOn.singleton (Q 0)) (bC k) (centerB k (p k).last (p k).last_mem).symm
  let first := pc.join (p i) (Set.disjoint_union_left.mpr ⟨bB k i hki,(bC i).symm⟩)
    (by simpa [pc] using centerB i (p i).first (p i).first_mem)
  have firstW : Disjoint ((B k ∪ C) ∪ B i) W := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨bW k,cW⟩,bW i⟩
  have firstB : Disjoint ((B k ∪ C) ∪ B i) (B j) := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨bB k j hkj,(bC j).symm⟩,bB i j hij⟩
  have firstU : Disjoint ((B k ∪ C) ∪ B i) U := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨bU k,cU⟩,bU i⟩
  obtain ⟨path⟩ := PathOn.insert_on_two_joins first r (p j) firstW firstB (bW j).symm
    firstU wU (bU j)
    (by simpa [first] using (attB _ hrf i hm hmi _ (p i).last_mem).symm)
    (attB _ hrl j hn hnj _ (p j).first_mem) uInd
    (fun u hu => by simpa [first] using extraB i _ (p i).last_mem u hu)
    (fun u hu => ⟨attU _ hrf u hu,attU _ hrl u hu⟩)
    (fun u hu => (extraB j _ (p j).first_mem u hu).symm)
  have hUniv : ((((B k ∪ C) ∪ B i) ∪ W) ∪ B j) ∪ U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have inB (s : Fin 3) (hs : x ∈ B s) : x ∈ ((((B k ∪ C) ∪ B i) ∪ W) ∪ B j) ∪ U := by
      rcases hAll s with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (Or.inr hs)))
      · exact Or.inl (Or.inr hs)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hs))))
    by_cases ho : Outside Q x
    · rcases outside_near_or_far ho with hN | hF
      · by_cases ha : ∃ z : {w | Far G Q w}, G.Adj x z.val
        · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨hN,ha⟩)))
        · rcases outside x ⟨hN,ha⟩ with ⟨s,hs⟩ | hs
          · exact inB s (Set.mem_insert_of_mem _ hs)
          · exact Or.inr hs
      · exact Or.inl (Or.inl (Or.inr (Or.inr hF)))
    · unfold Outside at ho
      push_neg at ho
      obtain ⟨s,rfl⟩ := ho
      fin_cases s
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
      · exact inB 0 (Set.mem_insert _ _)
      · exact inB 1 (Set.mem_insert _ _)
      · exact inB 2 (Set.mem_insert _ _)
  exact (path.cast hUniv).traceable

#print axioms mixed_attachment_traceable

private theorem outside_relabel (e : Equiv.Perm (Fin 4)) (x : V) :
    Outside (e.toEmbedding.trans Q) x ↔ Outside Q x := by
  constructor
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact h j
  · intro h i
    exact h (e i)

private theorem near_relabel (e : Equiv.Perm (Fin 4)) (x : V) :
    Near G (e.toEmbedding.trans Q) x ↔ Near G Q x := by
  constructor
  · rintro ⟨h,i,ha⟩
    exact ⟨(outside_relabel e x).mp h,e i,ha⟩
  · rintro ⟨h,i,ha⟩
    obtain ⟨j,rfl⟩ := e.surjective i
    exact ⟨(outside_relabel e x).mpr h,j,ha⟩

private theorem far_relabel (e : Equiv.Perm (Fin 4)) (x : V) :
    Far G (e.toEmbedding.trans Q) x ↔ Far G Q x := by
  constructor
  · rintro ⟨h,hm⟩
    refine ⟨(outside_relabel e x).mp h,?_⟩
    intro i
    obtain ⟨j,rfl⟩ := e.surjective i
    have hf : ¬ G.Adj (Q (e j)) x := fun he => by
      have b := (hm j).mp he
      simp at b
    simpa using hf
  · rintro ⟨h,hm⟩
    refine ⟨(outside_relabel e x).mpr h,?_⟩
    intro i
    have hf : ¬ G.Adj (Q (e i)) x := fun he => by
      have b := (hm (e i)).mp he
      simp at b
    simpa using hf

private theorem attached_relabel (e : Equiv.Perm (Fin 4)) (x : V) :
    Attached G (e.toEmbedding.trans Q) x ↔ Attached G Q x := by
  constructor
  · rintro ⟨h,y,ha⟩
    exact ⟨(near_relabel e x).mp h,⟨y.val,(far_relabel e y.val).mp y.property⟩,ha⟩
  · rintro ⟨h,y,ha⟩
    exact ⟨(near_relabel e x).mpr h,⟨y.val,(far_relabel e y.val).mpr y.property⟩,ha⟩

private theorem mask_relabel {x : V} {m n : Mask} (hm : HasMask G Q x m)
    (e : Equiv.Perm (Fin 4))
    (he : ∀ i : Fin 4, m.val.testBit (e i).val = n.val.testBit i.val) :
    HasMask G (e.toEmbedding.trans Q) x n := by
  intro i
  change G.Adj (Q (e i)) x ↔ n.val.testBit i.val = true
  rw [← he i]
  exact hm (e i)

private theorem normalize_one_mask {m : Mask} (hm : AttachmentMask m) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = 0 ∧
      ∀ i : Fin 4, m.val.testBit (e i).val = (7 : Mask).val.testBit i.val := by
  rcases hm with rfl | rfl | rfl
  · exact ⟨Equiv.refl (Fin 4),by decide,by decide⟩
  · exact ⟨Equiv.swap (2 : Fin 4) 3,by decide,by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 3,by decide,by decide⟩

private theorem normalize_two_masks {m n : Mask} (hm : AttachmentMask m)
    (hn : AttachmentMask n) (hne : m ≠ n) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = 0 ∧
      (∀ i : Fin 4, m.val.testBit (e i).val = (7 : Mask).val.testBit i.val) ∧
      (∀ i : Fin 4, n.val.testBit (e i).val = (11 : Mask).val.testBit i.val) := by
  rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨Equiv.refl (Fin 4),by decide,by decide,by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 2,by decide,by decide,by decide⟩
  · exact ⟨Equiv.swap (2 : Fin 4) 3,by decide,by decide,by decide⟩
  · exact (hne rfl).elim
  · exact ⟨(Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap 1 2),by decide,by decide,by decide⟩
  · exact ⟨(Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap 1 3),by decide,by decide,by decide⟩
  · exact ⟨Equiv.swap (1 : Fin 4) 3,by decide,by decide,by decide⟩
  · exact (hne rfl).elim

/-- The nondominating-claw branch of Graffiti.pc #199 at connectivity two. -/
theorem nondominating_claw_traceable [Fintype V] (ht : treeNumber G ≤ 4)
    (hc : G.Connected) (hk : ConnectivityAtLeast G 2)
    (hq : IsClaw G Q) (hy : ∃ y, Far G Q y) : Traceable G := by
  classical
  obtain ⟨y,hy⟩ := hy
  have h := noTree5_of_treeNumber_le_four ht
  obtain ⟨x,hx,hxy⟩ := far_has_attachment h hq hc ⟨y,hy⟩
  have ax : Attached G Q x := ⟨hx,⟨y,hy⟩,hxy⟩
  obtain ⟨m,hm⟩ := mask_exists G Q x
  have hM := near_far_attachment_mask h hq hx hy hxy hm
  by_cases hUniform : ∀ z, Attached G Q z → HasMask G Q z m
  · obtain ⟨e,h0,he⟩ := normalize_one_mask hM
    have hq' := isClaw_relabel hq e h0
    have hy' := (far_relabel e y).mpr hy
    refine uniform_attachment_traceable h hq' hc hk ⟨y,hy'⟩ ?_
    intro z hz
    exact mask_relabel (hUniform z ((attached_relabel e z).mp hz)) e he
  · push_neg at hUniform
    obtain ⟨z,hz,hzm⟩ := hUniform
    obtain ⟨n,hn⟩ := mask_exists G Q z
    have hne : m ≠ n := fun he => hzm (he.symm ▸ hn)
    obtain ⟨f,hzf⟩ := hz.2
    have hN := near_far_attachment_mask h hq hz.1 f.property hzf hn
    obtain ⟨e,h0,he,he'⟩ := normalize_two_masks hM hN hne
    exact mixed_attachment_traceable h (isClaw_relabel hq e h0) hc hk
      ⟨x,(attached_relabel e x).mpr ax,mask_relabel hm e he⟩
      ⟨z,(attached_relabel e z).mpr hz,mask_relabel hn e he'⟩

/-- Exact connectivity-two specialization with an induced claw which fails to dominate. -/
theorem conjecture199_connectivity_two_of_nondominating_claw [Fintype V] [Nonempty V]
    (hc : G.Connected) (hk : vertexConnectivity G = 2) (ht : treeNumber G ≤ 4)
    (hq : IsClaw G Q) (hy : ∃ y, Far G Q y) : Traceable G := by
  have hconn : ConnectivityAtLeast G 2 := hk ▸ connectivityAtLeast_vertexConnectivity G
  exact nondominating_claw_traceable ht hc hconn hq hy

#print axioms nondominating_claw_traceable
#print axioms conjecture199_connectivity_two_of_nondominating_claw

end Graffiti199K2


namespace Graffiti199K2
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private structure Longest (G : SimpleGraph V) (P : List V) : Prop where
  nonempty : P ≠ []
  chain : List.Chain' G.Adj P
  nodup : P.Nodup
  maximal : ∀ L : List V, List.Chain' G.Adj L → L.Nodup → L.length ≤ P.length

private theorem longest_exists [Fintype V] (a : V) : ∃ P, Longest G P := by
  classical
  let U := Fintype.card V
  let P (n : ℕ) : Prop := ∃ l : List V, l.length = n ∧ List.Chain' G.Adj l ∧ l.Nodup
  have h1 : P 1 := ⟨[a],rfl,by simp,by simp⟩
  have hU : 1 ≤ U := Fintype.card_pos_iff.mpr ⟨a⟩
  obtain ⟨l,hl,hc,hn⟩ := Nat.findGreatest_spec hU h1
  have hsize : 1 ≤ Nat.findGreatest P U := Nat.le_findGreatest hU h1
  refine ⟨l,⟨fun he => by simp [he] at hl; omega,hc,hn,?_⟩⟩
  intro L hL hLn
  rw [hl]
  exact Nat.le_findGreatest hLn.length_le_card ⟨L,rfl,hL,hLn⟩

private theorem attach_chain {A B : List V} (hA : List.Chain' G.Adj A) (hB : List.Chain' G.Adj B)
    (hAn : A ≠ []) (hBn : B ≠ [])
    (he : G.Adj (A.getLast hAn) (B.head hBn)) : List.Chain' G.Adj (A ++ B) := by
  apply hA.append hB
  intro x hx y hy
  rw [List.getLast?_eq_getLast hAn,Option.mem_some_iff] at hx
  rw [List.head?_eq_head hBn,Option.mem_some_iff] at hy
  exact hx ▸ hy ▸ he

private theorem reverse_chain {P : List V} (hc : List.Chain' G.Adj P) :
    List.Chain' G.Adj P.reverse :=
  List.chain'_reverse.mpr (List.Chain'.imp (fun _ _ h => h.symm) hc)

private theorem no_extension {P L X : List V} (hh : Longest G P)
    (hc : List.Chain' G.Adj L) (hperm : L.Perm (P ++ X)) (hx : X ≠ [])
    (hn : X.Nodup) (hf : ∀ x ∈ X, x ∉ P) : False := by
  have hnodup : L.Nodup := hperm.nodup_iff.mpr
    (List.nodup_append.mpr ⟨hh.nodup,hn,fun x hp hX => hf x hX hp⟩)
  have le := hh.maximal L hc hnodup
  have he := hperm.length_eq
  simp only [List.length_append] at he
  have hn' : X.length ≠ 0 := fun he => hx (List.length_eq_zero_iff.mp he)
  omega

private theorem endpoints_miss_outside {P : List V} (hh : Longest G P) {x : V} (hx : x ∉ P) :
    ¬ G.Adj (P.head hh.nonempty) x ∧ ¬ G.Adj (P.getLast hh.nonempty) x := by
  constructor
  · intro he
    have hc : List.Chain' G.Adj ([x] ++ P) :=
      attach_chain (by simp) hh.chain (by simp) hh.nonempty he.symm
    exact no_extension hh hc List.perm_append_comm (by simp) (by simp)
      (fun v hv => by simpa using (List.mem_singleton.mp hv).symm ▸ hx)
  · intro he
    have hc : List.Chain' G.Adj (P ++ [x]) :=
      attach_chain hh.chain (by simp) hh.nonempty (by simp) he
    exact no_extension hh hc (.refl _) (by simp) (by simp)
      (fun v hv => by simpa using (List.mem_singleton.mp hv).symm ▸ hx)

private theorem successor_rotation {P A B C : List V} (hh : Longest G P) (hp : P = A ++ B)
    (hA : A ≠ []) (hC : C ≠ []) (hperm : C.Perm B) (hchain : List.Chain' G.Adj C)
    {x : V} (hx : x ∉ P) (hxc : G.Adj (A.getLast hA) x)
    (he : G.Adj (C.getLast hC) (A.head hA)) : False := by
  have ha : List.Chain' G.Adj A := (hp ▸ hh.chain).left_of_append
  have hca : List.Chain' G.Adj (C ++ A) := attach_chain hchain ha hC hA he
  have hcn := List.append_ne_nil_of_left_ne_nil hC A
  have hfinal : List.Chain' G.Adj ((C ++ A) ++ [x]) := attach_chain hca (by simp) hcn (by simp)
    (by simpa only [List.getLast_append_of_ne_nil _ hA] using hxc)
  have pp : (C ++ A).Perm P := by
    rw [hp]
    exact (hperm.append_right A).trans List.perm_append_comm
  exact no_extension hh hfinal (pp.append_right _) (by simp) (by simp) (fun v hv => by
    obtain rfl := List.mem_singleton.mp hv
    exact hx)

private theorem walk_crosses {a b : V} (w : G.Walk a b) (S : Set V) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  classical
  induction w with
  | nil => exact (hb ha).elim
  | @cons a b c hab _ ih =>
    by_cases h : b ∈ S
    · exact ih h hb
    · exact ⟨a,ha,b,h,hab⟩

private theorem graph_crosses (hc : G.Connected) (S : Set V) (a b : V) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  obtain ⟨w⟩ := hc a b
  exact walk_crosses w S ha hb

private theorem cut_attachments [Fintype V] {P : List V} (hh : Longest G P)
    (hk : ConnectivityAtLeast G 2) (hc : G.Connected) {w : V} (hw : w ∉ P) :
    ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧
      (∃ x ∉ P, G.Adj a x) ∧ (∃ y ∉ P, G.Adj b y) := by
  classical
  let f := P.head hh.nonempty
  have hf : f ∈ P := List.head_mem _
  obtain ⟨a,ha,x,hx,he⟩ := graph_crosses hc {v | v ∈ P} f w hf hw
  have hfa : f ≠ a := by
    intro heq
    have ha' : G.Adj f x := heq.symm ▸ he
    exact (endpoints_miss_outside hh hx).1 ha'
  let S : Finset V := {a}
  let C : Set V := (↑S : Set V)ᶜ
  let H := G.induce C
  have hConn : H.Connected := hk.2 S (by simp [S])
  have hfc : f ∈ C := by simpa [C,S] using hfa
  have hwc : w ∈ C := by simpa [C,S] using (show w ≠ a from fun he => hw (he.symm ▸ ha))
  obtain ⟨b,hb,y,hy,he'⟩ :=
    graph_crosses hConn ({v : C | v.val ∈ P} : Set C) ⟨f,hfc⟩ ⟨w,hwc⟩ hf hw
  have hba : b.val ≠ a := by simpa [C,S] using b.property
  exact ⟨a,ha,b.val,hb,hba.symm,⟨x,hx,he⟩,⟨y.val,hy,he'⟩⟩


private def Ear (G : SimpleGraph V) (P : List V) (x y : V) : Prop :=
  ∃ (X : List V) (hn : X ≠ []), X.Nodup ∧ List.Chain' G.Adj X ∧
    (∀ v ∈ X, v ∉ P) ∧ G.Adj x (X.head hn) ∧ G.Adj (X.getLast hn) y

private theorem outside_ear {P : List V} {a b s t : V}
    (hs : s ∉ P) (ht : t ∉ P) (as' : G.Adj a s) (bt : G.Adj b t)
    (hcl : ∀ ⦃x y⦄, x ∉ P → y ∉ P → x ≠ y → G.Adj x y) : Ear G P a b := by
  classical
  by_cases he : s = t
  · subst t
    exact ⟨[s],by simp,by simp,by simp,by simpa,as',bt.symm⟩
  · exact ⟨[s,t],by simp,by simp [he],List.chain'_pair.mpr (hcl hs ht he),
      fun v hv => by
        rcases (show v = s ∨ v = t by simpa using hv) with rfl | rfl
        · exact hs
        · exact ht,
      as',bt.symm⟩

private theorem no_ear_between_consecutive {P A B : List V} (hh : Longest G P) (hp : P = A ++ B)
    (hA : A ≠ []) (hB : B ≠ []) (he : Ear G P (A.getLast hA) (B.head hB)) : False := by
  obtain ⟨X,hn,hdup,hchain,hout,hAX,hXB⟩ := he
  have ha : List.Chain' G.Adj A := (hp ▸ hh.chain).left_of_append
  have hb : List.Chain' G.Adj B := (hp ▸ hh.chain).right_of_append
  have hAXc := attach_chain ha hchain hA hn hAX
  have han := List.append_ne_nil_of_left_ne_nil hA X
  have hc := attach_chain hAXc hb han hB (by simpa only [List.getLast_append_of_ne_nil _ hn] using hXB)
  have pp : ((A ++ X) ++ B).Perm (P ++ X) := by
    rw [hp,List.append_assoc,List.append_assoc]
    exact List.Perm.append_left A List.perm_append_comm
  exact no_extension hh hc pp hn hdup hout

private theorem split_after {P : List V} {x : V} (hh : Longest G P) (hx : x ∈ P)
    (hLast : x ≠ P.getLast hh.nonempty) :
    ∃ (A B : List V) (hA : A ≠ []) (_ : B ≠ []), P = A ++ B ∧ A.getLast hA = x := by
  obtain ⟨L,R,he⟩ := List.append_of_mem hx
  have hL : L ++ [x] ≠ [] := by simp
  have hR : R ≠ [] := by
    intro hr
    subst R
    exact hLast (by simp [he,List.getLast_append_singleton])
  exact ⟨L ++ [x],R,hL,hR,by simp [he,List.append_assoc],List.getLast_append_singleton _⟩

private theorem successor_constraints {P A B : List V} (hh : Longest G P) (hp : P = A ++ B)
    (hA : A ≠ []) (hB : B ≠ []) {x : V} (hx : x ∉ P) (hAx : G.Adj (A.getLast hA) x)
    (hcl : ∀ ⦃x y⦄, x ∉ P → y ∉ P → x ≠ y → G.Adj x y) :
    (∀ y ∉ P, ¬ G.Adj (B.head hB) y) ∧ ¬ G.Adj (P.head hh.nonempty) (B.head hB) := by
  constructor
  · intro y hy hBy
    exact no_ear_between_consecutive hh hp hA hB (outside_ear hx hy hAx hBy hcl)
  · intro he
    have hR : B.reverse ≠ [] := by simpa using hB
    have hFirst : P.head hh.nonempty = A.head hA := by
      simp [hp,List.head_append_of_ne_nil hA]
    have hedge : G.Adj (B.reverse.getLast hR) (A.head hA) := by
      simpa only [List.getLast_reverse,← hFirst] using he.symm
    have hc : List.Chain' G.Adj B := (hp ▸ hh.chain).right_of_append
    exact successor_rotation hh hp hA hR (List.reverse_perm B) (reverse_chain hc) hx hAx hedge

private theorem ordered_split {P : List V} {x y : V} (hx : x ∈ P) (hy : y ∈ P) (hne : x ≠ y) :
    (∃ L M R, P = L ++ x :: M ++ y :: R) ∨ (∃ L M R, P = L ++ y :: M ++ x :: R) := by
  obtain ⟨L,R,hp⟩ := List.append_of_mem hx
  rw [hp,List.mem_append,List.mem_cons] at hy
  rcases hy with hL | hEq | hR
  · obtain ⟨L',M,hLL'⟩ := List.append_of_mem hL
    exact Or.inr ⟨L',M,R,by simp [hp,hLL',List.append_assoc]⟩
  · exact (hne hEq.symm).elim
  · obtain ⟨M,R',hRR'⟩ := List.append_of_mem hR
    exact Or.inl ⟨L,M,R',by simp [hp,hRR']⟩

private theorem independent_four_of_vertices {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d)
    (nbc : ¬ G.Adj b c) (nbd : ¬ G.Adj b d) (ncd : ¬ G.Adj c d) :
    ∃ I, IndependentFour G I := by
  let f : Fin 4 → V := ![a,b,c,d]
  have hf : List.ofFn f = [a,b,c,d] := by
    rfl
  have hn : (List.ofFn f).Nodup := by rw [hf]; simp [hab,hac,had,hbc,hbd,hcd]
  refine ⟨⟨f,List.nodup_ofFn.mp hn⟩,?_⟩
  have nba : ¬ G.Adj b a := fun h => nab h.symm
  have nca : ¬ G.Adj c a := fun h => nac h.symm
  have nda : ¬ G.Adj d a := fun h => nad h.symm
  have ncb : ¬ G.Adj c b := fun h => nbc h.symm
  have ndb : ¬ G.Adj d b := fun h => nbd h.symm
  have ndc : ¬ G.Adj d c := fun h => ncd h.symm
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f,nab,nac,nad,nbc,nbd,ncd,nba,nca,nda,ncb,ndb,ndc]

private theorem ordered_attachments_force_independent_four {P L M R : List V} {a b x y w : V}
    (hh : Longest G P) (hp : P = L ++ a :: M ++ b :: R)
    (hx : x ∉ P) (hy : y ∉ P) (hw : w ∉ P) (hax : G.Adj a x) (hby : G.Adj b y)
    (hcl : ∀ ⦃x y⦄, x ∉ P → y ∉ P → x ≠ y → G.Adj x y) :
    ∃ I, IndependentFour G I := by
  let A := L ++ [a]
  let B := M ++ [b]
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  have hAlast : A.getLast hA = a := List.getLast_append_singleton _
  have hBlast : B.getLast hB = b := List.getLast_append_singleton _
  have hp' : P = A ++ (B ++ R) := by simp [hp,A,B,List.append_assoc]
  have hp'' : P = (A ++ B) ++ R := by rw [List.append_assoc,← hp']
  have hR : R ≠ [] := by
    intro hn
    have last : P.getLast hh.nonempty = b := by
      simp [hp'',hn,List.getLast_append_of_ne_nil _ hB,hBlast]
    exact (endpoints_miss_outside hh hy).2 (last.symm ▸ hby)
  have hBR : B ++ R ≠ [] := List.append_ne_nil_of_left_ne_nil hB R
  have hAB : A ++ B ≠ [] := List.append_ne_nil_of_left_ne_nil hA B
  let u := P.head hh.nonempty
  let s := B.head hB
  let t := R.head hR
  have hFirst : u = A.head hA := by simp [u,hp',List.head_append_of_ne_nil hA]
  have hS : s = (B ++ R).head hBR := (List.head_append_of_ne_nil hB).symm
  have hsOut :=
    successor_constraints hh hp' hA hBR hx (hAlast.symm ▸ hax) hcl
  have htOut :=
    successor_constraints hh hp'' hAB hR hy
      (by simpa only [List.getLast_append_of_ne_nil _ hB,hBlast] using hby) hcl
  have hnST : ¬ G.Adj s t := by
    intro he
    obtain ⟨X,hX,hXD,hXC,hOutside,hAX,hXB⟩ := outside_ear hx hy hax hby hcl
    have hPc : List.Chain' G.Adj (A ++ (B ++ R)) := hp' ▸ hh.chain
    have hRev : B.reverse ≠ [] := by simpa using hB
    have hAXc := attach_chain hPc.left_of_append hXC hA hX (hAlast.symm ▸ hAX)
    have hAXn := List.append_ne_nil_of_left_ne_nil hA X
    have hAXb := attach_chain hAXc (reverse_chain hPc.right_of_append.left_of_append)
      hAXn hRev (by simpa only [List.getLast_append_of_ne_nil _ hX,List.head_reverse,hBlast] using hXB)
    have hAXbn := List.append_ne_nil_of_left_ne_nil hAXn B.reverse
    have hFinal := attach_chain hAXb hPc.right_of_append.right_of_append hAXbn hR
      (by simpa only [List.getLast_append_of_ne_nil _ hRev,List.getLast_reverse] using he)
    have p1 : (((A ++ X) ++ B.reverse) ++ R).Perm (((A ++ X) ++ B) ++ R) :=
      ((List.reverse_perm B).append_left (A ++ X)).append_right R
    have p2 : (((A ++ X) ++ B) ++ R).Perm (P ++ X) := by
      rw [hp']
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := X) (l₂ := B ++ R)).append_left A
    exact no_extension hh hFinal (p1.trans p2) hX hXD hOutside
  have huA : u ∈ A := hFirst.symm ▸ List.head_mem hA
  have hsB : s ∈ B := List.head_mem hB
  have htR : t ∈ R := List.head_mem hR
  have dA : List.Disjoint A (B ++ R) := List.disjoint_of_nodup_append (hp' ▸ hh.nodup)
  have dBR : List.Disjoint B R :=
    List.disjoint_of_nodup_append (List.nodup_append.mp (hp' ▸ hh.nodup)).2.1
  have hu : u ∈ P := List.head_mem _
  have hs : s ∈ P := by rw [hp']; exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hsB)))
  have ht : t ∈ P := by rw [hp']; exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr htR)))
  have hus : u ≠ s := fun he => dA huA (List.mem_append.mpr (Or.inl (he.symm ▸ hsB)))
  have hut : u ≠ t := fun he => dA huA (List.mem_append.mpr (Or.inr (he.symm ▸ htR)))
  have hst : s ≠ t := fun he => dBR hsB (he.symm ▸ htR)
  exact independent_four_of_vertices (a := u) (b := s) (c := t) (d := w) hus hut (fun he => hw (he ▸ hu))
    hst (fun he => hw (he ▸ hs)) (fun he => hw (he ▸ ht))
    (hS.symm ▸ hsOut.2) htOut.2 (endpoints_miss_outside hh hw).1
    hnST (hS.symm ▸ hsOut.1 w hw) (htOut.1 w hw)

/-- A direct connectivity-two instance of the Chvátal–Erdős path theorem. -/
theorem traceable_of_no_independent_four [Fintype V] (hc : G.Connected)
    (hk : ConnectivityAtLeast G 2) (hI : ∀ I, ¬ IndependentFour G I) : Traceable G := by
  classical
  obtain ⟨a₀⟩ := hc.nonempty
  obtain ⟨P,hh⟩ := longest_exists (G := G) a₀
  by_cases hAll : ∀ x, x ∈ P
  · exact traceable_of_spanning_chain P hh.nonempty hh.chain hh.nodup hAll
  push_neg at hAll
  obtain ⟨w,hw⟩ := hAll
  obtain ⟨a,ha,b,hb,hab,⟨x,hx,hax⟩,⟨y,hy,hby⟩⟩ := cut_attachments hh hk hc hw
  let u := P.head hh.nonempty
  let v := P.getLast hh.nonempty
  have hau : a ≠ v := by
    intro he
    have he' : G.Adj v x := he ▸ hax
    exact (endpoints_miss_outside hh hx).2 he'
  obtain ⟨A,B,hA,hB,hp,hal⟩ := split_after hh ha hau
  have hU : u = A.head hA := by simp [u,hp,List.head_append_of_ne_nil hA]
  have hV : v = B.getLast hB := by simp [v,hp,List.getLast_append_of_ne_nil _ hB]
  have hu : u ∈ P := List.head_mem _
  have hv : v ∈ P := List.getLast_mem _
  have huv : u ≠ v := by
    intro he
    have hd := List.disjoint_of_nodup_append (hp ▸ hh.nodup)
    exact hd (hU.symm ▸ List.head_mem hA) (he.symm ▸ hV.symm ▸ List.getLast_mem hB)
  have hUV : ¬ G.Adj u v := by
    intro had
    have hChain : List.Chain' G.Adj B := (hp ▸ hh.chain).right_of_append
    exact successor_rotation hh hp hA hB (.refl _) hChain hx (hal.symm ▸ hax)
      (by simpa only [← hU,← hV] using had.symm)
  have hOutside : ∀ ⦃x y⦄, x ∉ P → y ∉ P → x ≠ y → G.Adj x y := by
    intro a b ha hb hab
    by_cases he : G.Adj a b
    · exact he
    exfalso
    obtain ⟨I,hi⟩ := independent_four_of_vertices (a := u) (b := v) (c := a) (d := b) huv
      (fun e => ha (e ▸ hu)) (fun e => hb (e ▸ hu))
      (fun e => ha (e ▸ hv)) (fun e => hb (e ▸ hv)) hab hUV
      (endpoints_miss_outside hh ha).1 (endpoints_miss_outside hh hb).1
      (endpoints_miss_outside hh ha).2 (endpoints_miss_outside hh hb).2 he
    exact hI I hi
  rcases ordered_split ha hb hab with ⟨L,M,R,he⟩ | ⟨L,M,R,he⟩
  · obtain ⟨I,hi⟩ := ordered_attachments_force_independent_four hh he hx hy hw hax hby hOutside
    exact (hI I hi).elim
  · obtain ⟨I,hi⟩ := ordered_attachments_force_independent_four hh he hy hx hw hby hax hOutside
    exact (hI I hi).elim

/-- The dominating-claw branch of Graffiti.pc #199 at connectivity two. -/
theorem dominating_claw_traceable [Fintype V] (hc : G.Connected) (hk : ConnectivityAtLeast G 2)
    (ht : treeNumber G ≤ 4) (hd : EveryClawDominates G)
    (Q : Fin 4 ↪ V) (hq : IsClaw G Q) : Traceable G :=
  traceable_of_no_independent_four hc hk
    (treeNumber_le_four_excludes_independent_four_of_dominating_claws ht hd Q hq)

#print axioms traceable_of_no_independent_four
#print axioms dominating_claw_traceable

/-- The connectivity-two statement for every graph containing an induced claw. -/
theorem conjecture199_connectivity_two_of_induced_claw [Fintype V] [Nonempty V]
    (hc : G.Connected) (hk : vertexConnectivity G = 2) (ht : treeNumber G ≤ 4)
    (hclaw : ∃ Q : Fin 4 ↪ V, IsClaw G Q) : Traceable G := by
  classical
  have hconn : ConnectivityAtLeast G 2 := hk ▸ connectivityAtLeast_vertexConnectivity G
  by_cases hd : EveryClawDominates G
  · obtain ⟨Q,hQ⟩ := hclaw
    exact dominating_claw_traceable hc hconn ht hd Q hQ
  · unfold EveryClawDominates at hd
    push_neg at hd
    obtain ⟨Q,hQ,y,ho,hn⟩ := hd
    have hf : Far G Q y := ⟨ho,fun i => iff_of_false (hn i) (by simp)⟩
    exact nondominating_claw_traceable ht hc hconn hQ ⟨y,hf⟩

#print axioms conjecture199_connectivity_two_of_induced_claw

/-- The remaining Lean goal only concerns claw-free graphs with an independent four-set. -/
theorem conjecture199_connectivity_two_remaining [Fintype V] [Nonempty V]
    (hc : G.Connected) (hk : vertexConnectivity G = 2) (ht : treeNumber G ≤ 4)
    (hf : ¬ Traceable G) :
    (∀ Q : Fin 4 ↪ V, ¬ IsClaw G Q) ∧ (∃ I, IndependentFour G I) := by
  classical
  have hconn : ConnectivityAtLeast G 2 := hk ▸ connectivityAtLeast_vertexConnectivity G
  refine ⟨fun Q hQ => hf (conjecture199_connectivity_two_of_induced_claw hc hk ht ⟨Q,hQ⟩),?_⟩
  by_contra hn
  push_neg at hn
  exact hf (traceable_of_no_independent_four hc hconn hn)

#print axioms conjecture199_connectivity_two_remaining

end Graffiti199K2


namespace Graffiti199K2
namespace ClawFreeCase

open SimpleGraph
variable {V I : Type*} {G : SimpleGraph V}

def ClawFree (G : SimpleGraph V) : Prop := ∀ Q : Fin 4 ↪ V, ¬ IsClaw G Q

private theorem forbidClaw (hc : ClawFree G) {c a b d : V}
    (ha : G.Adj c a) (hb : G.Adj c b) (hd : G.Adj c d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (nab : ¬ G.Adj a b) (nad : ¬ G.Adj a d) (nbd : ¬ G.Adj b d) : False := by
  let f : Fin 4 → V := ![c,a,b,d]
  have hno : (List.ofFn f).Nodup := by
    change [c,a,b,d].Nodup
    simp [ha.ne,hb.ne,hd.ne,hab,had,hbd]
  apply hc ⟨f,List.nodup_ofFn.mp hno⟩
  have nba : ¬ G.Adj b a := fun h => nab h.symm
  have nda : ¬ G.Adj d a := fun h => nad h.symm
  have ndb : ¬ G.Adj d b := fun h => nbd h.symm
  change ∀ i j : Fin 4, G.Adj (f i) (f j) ↔
    decide ((i.val = 0 ∧ 0 < j.val) ∨ (j.val = 0 ∧ 0 < i.val)) = true
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f,ha,hb,hd,ha.symm,hb.symm,hd.symm,nab,nad,nbd,nba,nda,ndb]

private theorem forbidP5 (ht : NoTree5 G) {a b c d e : V}
    (hN : [a,b,c,d,e].Nodup)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e)
    (ac : ¬ G.Adj a c) (ad : ¬ G.Adj a d) (ae : ¬ G.Adj a e)
    (bd : ¬ G.Adj b d) (be : ¬ G.Adj b e) (ce : ¬ G.Adj c e) : False := by
  let f : Fin 5 → V := ![a,b,c,d,e]
  have hf : (List.ofFn f).Nodup := hN
  apply ht 0 ⟨f,List.nodup_ofFn.mp hf⟩
  change ∀ i j : Fin 5, G.Adj (f i) (f j) ↔ decide (min i.val j.val + 1 = max i.val j.val) = true
  have ca : ¬ G.Adj c a := fun h => ac h.symm
  have da : ¬ G.Adj d a := fun h => ad h.symm
  have ea : ¬ G.Adj e a := fun h => ae h.symm
  have db : ¬ G.Adj d b := fun h => bd h.symm
  have eb : ¬ G.Adj e b := fun h => be h.symm
  have ec : ¬ G.Adj e c := fun h => ce h.symm
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f,ab,bc,cd,de,ab.symm,bc.symm,cd.symm,de.symm,ac,ad,ae,bd,be,ce,ca,da,ea,db,eb,ec]

def Touch (G : SimpleGraph V) (s : I ↪ V) (i : I) (x : V) : Prop :=
  x = s i ∨ G.Adj (s i) x

def Single (G : SimpleGraph V) (s : I ↪ V) (i : I) (x : V) : Prop :=
  Touch G s i x ∧ ∀ j : I, Touch G s j x → j = i

structure Frame (G : SimpleGraph V) (I : Type*) where
  s : I ↪ V
  indep : ∀ i j : I, ¬ G.Adj (s i) (s j)
  cover : ∀ x : V, ∃ i : I, Touch G s i x
  clique : ∀ i : I, ∀ ⦃x y : V⦄, Single G s i x → Single G s i y → x ≠ y → G.Adj x y
  claw : ClawFree G
  path : NoTree5 G

namespace Frame
variable (F : Frame G I)

abbrev Has (i : I) (x : V) := Touch G F.s i x
abbrev One (i : I) (x : V) := Single G F.s i x
def Two (i j : I) (x : V) := i ≠ j ∧ F.Has i x ∧ F.Has j x

def Double (i j : I) : Prop := ∃ x, F.Two i j x
def Link (i j : I) : Prop :=
  i ≠ j ∧ ∃ x y, F.One i x ∧ F.One j y ∧ G.Adj x y

private theorem has_s {i j : I} (h : F.Has i (F.s j)) : j = i := by
  rcases h with h | h
  · exact F.s.injective h
  · exact (F.indep i j h).elim

private theorem one_s (i : I) : F.One i (F.s i) :=
  ⟨Or.inl rfl,fun _ h => (F.has_s h).symm⟩

private theorem one_other {i j : I} {x : V} (hx : F.One i x) (hne : j ≠ i) :
    ¬ F.Has j x := fun h => hne (hx.2 j h)

private theorem distinct_of_has_miss {i : I} {x y : V} (hx : F.Has i x) (hy : ¬F.Has i y) :
    x ≠ y := fun e => hy (e ▸ hx)

private theorem two_outside {i j k : I} {x : V} (hx : F.Two i j x) : x ≠ F.s k := by
  intro h
  subst x
  exact hx.1 ((F.has_s hx.2.1).symm.trans (F.has_s hx.2.2))

private theorem two_edges {i j : I} {x : V} (hx : F.Two i j x) :
    G.Adj (F.s i) x ∧ G.Adj (F.s j) x := by
  exact ⟨hx.2.1.resolve_left (F.two_outside hx),hx.2.2.resolve_left (F.two_outside hx)⟩

private theorem two_miss {i j k : I} {x : V} (hx : F.Two i j x) (hki : k ≠ i) (hkj : k ≠ j) :
    ¬ F.Has k x := by
  intro h
  have he := h.resolve_left (F.two_outside hx)
  have ⟨hi,hj⟩ := F.two_edges hx
  exact forbidClaw F.claw hi.symm hj.symm he.symm
    (F.s.injective.ne hx.1) (F.s.injective.ne hki.symm) (F.s.injective.ne hkj.symm)
    (F.indep i j) (F.indep i k) (F.indep j k)

private theorem not_adj_to_two_other {i j : I} {x y : V}
    (hx : F.Two i j x) (hy : ¬F.Has i y) (hy' : ¬F.Has j y) : ¬ G.Adj x y := by
  intro he
  obtain ⟨hi,hj⟩ := F.two_edges hx
  exact forbidClaw F.claw hi.symm hj.symm he (F.s.injective.ne hx.1)
    (fun he => hy (Or.inl he.symm)) (fun he => hy' (Or.inl he.symm))
    (F.indep i j) (fun he => hy (Or.inr he)) (fun he => hy' (Or.inr he))

private theorem two_symm {i j : I} {x : V} (hx : F.Two i j x) : F.Two j i x :=
  ⟨hx.1.symm,hx.2.2,hx.2.1⟩

private theorem either_one_or_two (x : V) : (∃ i, F.One i x) ∨ ∃ i j, F.Two i j x := by
  classical
  obtain ⟨i,hi⟩ := F.cover x
  by_cases h : ∀ j, F.Has j x → j = i
  · exact Or.inl ⟨i,hi,h⟩
  · push_neg at h
    obtain ⟨j,hj,hne⟩ := h
    exact Or.inr ⟨i,j,hne.symm,hi,hj⟩

private theorem one_ne_of_labels {i j : I} {x y : V} (hi : F.One i x) (hj : F.One j y)
    (hne : i ≠ j) : x ≠ y := F.distinct_of_has_miss hi.1 (F.one_other hj hne)

private theorem one_ne_two {i j k : I} {x y : V} (hx : F.One i x) (hy : F.Two j k y) : x ≠ y := by
  intro e
  subst x
  exact hy.1 ((hx.2 j hy.2.1).trans (hx.2 k hy.2.2).symm)

private theorem one_ne_s {i j : I} {x : V} (hx : F.One i x) (hne : i ≠ j) : x ≠ F.s j := by
  intro e
  exact hne (F.has_s (e ▸ hx.1)).symm

private theorem one_edge {i j : I} {x y : V} (hx : F.One i x) (hy : F.One j y)
    (hne : i ≠ j) (he : G.Adj x y) : G.Adj (F.s i) x ∧ G.Adj (F.s j) y := by
  refine ⟨hx.1.resolve_left ?_,hy.1.resolve_left ?_⟩
  · intro e
    exact F.one_other hy hne (Or.inr (e ▸ he))
  · intro e
    exact F.one_other hx hne.symm (Or.inr (e ▸ he.symm))

private theorem double_ne {i j : I} (h : F.Double i j) : i ≠ j := by
  obtain ⟨_,he⟩ := h
  exact he.1

private theorem double_symm {i j : I} (h : F.Double i j) : F.Double j i := by
  obtain ⟨v,hv⟩ := h
  exact ⟨v,F.two_symm hv⟩

private theorem link_symm {i j : I} (h : F.Link i j) : F.Link j i := by
  obtain ⟨hne,x,y,hx,hy,he⟩ := h
  exact ⟨hne.symm,y,x,hy,hx,he.symm⟩

private theorem incident_double_blocks_link {i j k : I} (hd : F.Double i j) (hl : F.Link i k) :
    k = j := by
  classical
  by_contra hn
  have hkj : k ≠ j := hn
  obtain ⟨u,hu⟩ := hd
  obtain ⟨hik,x,y,hx,hy,hxy⟩ := hl
  have hij := hu.1
  have hit := F.two_edges hu
  have hux : ¬ G.Adj u x := by
    intro he
    have huny := F.not_adj_to_two_other hu (F.one_other hy hik) (F.one_other hy hkj.symm)
    have kx := F.one_edge hx hy hik hxy
    have hNu : [F.s j,u,x,y,F.s k].Nodup := by
      simp [F.two_outside hu, (F.two_outside hu (k := j)).symm,
        (F.one_ne_s hx hij).symm, (F.one_ne_s hy hkj).symm,
        F.s.injective.ne hkj.symm, (F.one_ne_two hx hu).symm, (F.one_ne_two hy hu).symm,
        F.one_ne_of_labels hx hy hik,F.one_ne_s hx hik,kx.2.ne.symm]
    exact forbidP5 F.path hNu hit.2 he hxy kx.2.symm
      (fun q => F.one_other hx hij.symm (Or.inr q))
      (fun q => F.one_other hy hkj.symm (Or.inr q)) (F.indep j k)
      huny (fun q => F.two_miss hu hik.symm hkj (Or.inr q.symm))
      (fun q => F.one_other hx hik.symm (Or.inr q.symm))
  have hxAdj := (F.one_edge hx hy hik hxy).1
  have hNu : [F.s j,u,F.s i,x,y].Nodup := by
    simp [F.two_outside hu,(F.two_outside hu (k := j)).symm,F.s.injective.ne hij.symm,
      (F.one_ne_s hx hij).symm,(F.one_ne_s hy hkj).symm,(F.one_ne_two hx hu).symm,
      (F.one_ne_two hy hu).symm,hxAdj.ne,(F.one_ne_s hy hik.symm).symm,
      F.one_ne_of_labels hx hy hik]
  exact forbidP5 F.path hNu hit.2 hit.1.symm hxAdj hxy
    (F.indep j i) (fun h => F.one_other hx hij.symm (Or.inr h))
    (fun h => F.one_other hy hkj.symm (Or.inr h)) hux
    (F.not_adj_to_two_other hu (F.one_other hy hik) (F.one_other hy hkj.symm))
    (fun h => F.one_other hy hik (Or.inr h))

private theorem adjacent_pairs {i j k : I} {x y : V} (hx : F.Two i j x)
    (hy : F.Two j k y) (hik : i ≠ k) : G.Adj x y := by
  classical
  by_contra he
  have hxm := F.two_miss hx hik.symm hy.1.symm
  have hym := F.two_miss hy hx.1 hik
  have hne := F.distinct_of_has_miss hx.2.1 hym
  have hNu : [F.s i,x,F.s j,y,F.s k].Nodup := by
    simp [F.two_outside hx,F.two_outside hy,(F.two_outside hx (k := i)).symm,
      (F.two_outside hy (k := i)).symm,(F.two_outside hy (k := j)).symm,
      F.s.injective.ne hx.1,F.s.injective.ne hy.1,F.s.injective.ne hik,hne]
  exact forbidP5 F.path hNu (F.two_edges hx).1 (F.two_edges hx).2.symm
    (F.two_edges hy).1 (F.two_edges hy).2.symm (F.indep i j)
    (fun h => hym (Or.inr h)) (F.indep i k) he (fun h => hxm (Or.inr h.symm)) (F.indep j k)

private theorem double_no_path_three {i j k l : I} (hij : F.Double i j)
    (hjk : F.Double j k) (hkl : F.Double k l) (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) :
    False := by
  obtain ⟨x,hx⟩ := hij
  obtain ⟨y,hy⟩ := hjk
  obtain ⟨z,hz⟩ := hkl
  have mxz := F.two_miss hz hik hil
  have mxz' := F.two_miss hz hy.1 hjl
  have mxy := F.two_miss hy hx.1 hik
  have mzy := F.two_miss hy hjl.symm hz.1.symm
  have mxl := F.two_miss hx hil.symm hjl.symm
  have hNu : [F.s i,x,y,z,F.s l].Nodup := by
    simp [F.two_outside hx,F.two_outside hy,F.two_outside hz,
      (F.two_outside hx (k := i)).symm,(F.two_outside hy (k := i)).symm,
      (F.two_outside hz (k := i)).symm,F.s.injective.ne hil,
      F.distinct_of_has_miss hx.2.1 mxy,F.distinct_of_has_miss hx.2.1 mxz,
      (F.distinct_of_has_miss hz.2.2 mzy).symm]
  exact forbidP5 F.path hNu (F.two_edges hx).1 (F.adjacent_pairs hx hy hik)
    (F.adjacent_pairs hy hz hjl) (F.two_edges hz).2.symm (fun he => mxy (Or.inr he))
    (fun he => mxz (Or.inr he)) (F.indep i l) (F.not_adj_to_two_other hx mxz mxz')
    (fun he => mxl (Or.inr he.symm)) (fun he => mzy (Or.inr he.symm))

private theorem crosses_walk {x y : V} (p : G.Walk x y) (A : Set V) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ u ∈ A, ∃ v ∉ A, G.Adj u v := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons a b c ab _ ih =>
    by_cases hb : b ∈ A
    · exact ih hb hy
    · exact ⟨a,hx,b,hb,ab⟩

private theorem graph_cut (hc : G.Connected) (A : Set V) {x y : V} (hx : x ∈ A) (hy : y ∉ A) :
    ∃ u ∈ A, ∃ v ∉ A, G.Adj u v := by
  obtain ⟨p⟩ := hc x y
  exact crosses_walk p A hx hy

private theorem label_cut (hc : G.Connected) (T : Set I)
    (dclosed : ∀ i ∈ T, ∀ j ∉ T, ¬ F.Double i j)
    (lclosed : ∀ i ∈ T, ∀ j ∉ T, ¬ F.Link i j) (i : I) (hi : i ∈ T) :
    ∀ j : I, j ∈ T := by
  classical
  intro j
  by_contra hj
  let A : Set V := {v | ∃ i ∈ T, F.Has i v}
  have hs : F.s i ∈ A := ⟨i,hi,Or.inl rfl⟩
  have ht : F.s j ∉ A := by
    rintro ⟨k,hk,he⟩
    exact hj ((F.has_s he).symm ▸ hk)
  obtain ⟨x,hx,y,hy,he⟩ := graph_cut hc A hs ht
  have xAll (i : I) (h : F.Has i x) : i ∈ T := by
    by_contra hn
    obtain ⟨j,hj,h'⟩ := hx
    exact dclosed j hj i hn ⟨x,fun he => hn (he ▸ hj),h',h⟩
  have yNone (i : I) (hi : i ∈ T) : ¬ F.Has i y :=
    fun h => hy ⟨i,hi,h⟩
  rcases F.either_one_or_two x with ⟨i,hxi⟩ | ⟨i,j,ht⟩
  · rcases F.either_one_or_two y with ⟨j,hyj⟩ | ⟨j,k,ht⟩
    · have hi := xAll i hxi.1
      have hj : j ∉ T := fun h => yNone j h hyj.1
      exact lclosed i hi j hj ⟨fun he => hj (he ▸ hi),x,y,hxi,hyj,he⟩
    · have hmiss (k : I) (h : F.Has k y) : ¬ F.Has k x :=
        fun hx => yNone k (xAll k hx) h
      exact F.not_adj_to_two_other ht (hmiss j ht.2.1) (hmiss k ht.2.2) he.symm
  · exact F.not_adj_to_two_other ht (yNone i (xAll i ht.2.1)) (yNone j (xAll j ht.2.2)) he

private theorem singles_triangle {i j k : I} {x y z : V}
    (hx : F.One i x) (hy : F.One j y) (hz : F.One k z)
    (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k) (xy : G.Adj x y) (yz : G.Adj y z) :
    G.Adj x z := by
  classical
  by_contra nxz
  have sx := (F.one_edge hx hy ij xy).1
  have sz := (F.one_edge hy hz jk yz).2
  have hNu : [F.s i,x,y,z,F.s k].Nodup := by
    simp [sx.ne, (F.one_ne_s hy ij.symm).symm,(F.one_ne_s hz ik.symm).symm,
      F.s.injective.ne ik, xy.ne, F.one_ne_of_labels hx hz ik, F.one_ne_s hx ik,
      yz.ne, F.one_ne_s hy jk, sz.ne.symm]
  exact forbidP5 F.path hNu sx xy yz sz.symm
    (fun h => F.one_other hy ij (Or.inr h)) (fun h => F.one_other hz ik (Or.inr h)) (F.indep i k)
    nxz (fun h => F.one_other hx ik.symm (Or.inr h.symm))
    (fun h => F.one_other hy jk.symm (Or.inr h.symm))

private theorem singles_same_middle {i j k : I} {x x' y z : V}
    (hx : F.One i x) (hx' : F.One i x') (hy : F.One j y) (hz : F.One k z)
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (xy : G.Adj x y) (xz' : G.Adj x' z) :
    G.Adj x z ∧ G.Adj x' y ∧ G.Adj y z := by
  classical
  have yz : G.Adj y z := by
    by_contra nyz
    have nxz : ¬ G.Adj x z := fun e => nyz (F.singles_triangle hy hx hz ij.symm ik jk xy.symm e)
    have nyx' : ¬ G.Adj y x' := fun e => nyz (F.singles_triangle hy hx' hz ij.symm ik jk e xz')
    have xx' : G.Adj x x' := F.clique i hx hx' (fun e => nxz (e.symm ▸ xz'))
    have jy := (F.one_edge hx hy ij xy).2
    have hNu : [F.s j,y,x,x',z].Nodup := by
      simp [jy.ne,(F.one_ne_s hx ij).symm,(F.one_ne_s hx' ij).symm,(F.one_ne_s hz jk.symm).symm,
        xy.ne.symm,F.one_ne_of_labels hy hx' ij.symm,F.one_ne_of_labels hy hz jk,xx'.ne,
        F.one_ne_of_labels hx hz ik,xz'.ne]
    exact forbidP5 F.path hNu jy xy.symm xx' xz'
      (fun e => F.one_other hx ij.symm (Or.inr e)) (fun e => F.one_other hx' ij.symm (Or.inr e))
      (fun e => F.one_other hz jk (Or.inr e)) nyx' nyz nxz
  exact ⟨F.singles_triangle hx hy hz ij jk ik xy yz,
    F.singles_triangle hx' hz hy ik jk.symm ij xz' yz.symm,yz⟩

private theorem link_trans {i j k : I} (ij : F.Link i j) (jk : F.Link j k) (ik : i ≠ k) :
    F.Link i k := by
  obtain ⟨hij,x,y,hx,hy,xy⟩ := ij
  obtain ⟨hjk,y',z,hy',hz,yz⟩ := jk
  exact ⟨ik,x,z,hx,hz,(F.singles_same_middle hy hy' hx hz hij.symm hjk ik xy.symm yz).2.2⟩

def Active (i : I) (x : V) : Prop := F.One i x ∧
  ∃ j : I, ∃ y : V, i ≠ j ∧ F.One j y ∧ G.Adj x y

private theorem link_complete (hc : G.Connected) (hNoDouble : ∀ i j, ¬ F.Double i j)
    {i j : I} (hne : i ≠ j) : F.Link i j := by
  let T : Set I := {k | k = i ∨ F.Link i k}
  have all := F.label_cut hc T (fun i _ j _ => hNoDouble i j) (by
    intro a ha b hb h
    apply hb
    rcases ha with rfl | ha
    · exact Or.inr h
    · by_cases he : i = b
      · exact Or.inl he.symm
      · exact Or.inr (F.link_trans ha h he)) i (Or.inl rfl)
  exact (all j).resolve_left hne.symm

private theorem active_meets (hLink : ∀ i j, i ≠ j → F.Link i j)
    {i j : I} {x : V} (hx : F.Active i x) (hne : i ≠ j) :
    ∃ y, F.One j y ∧ G.Adj x y := by
  classical
  obtain ⟨hx,k,z,hik,hz,hxz⟩ := hx
  by_cases he : k = j
  · subst k
    exact ⟨z,hz,hxz⟩
  · obtain ⟨_,x',y,hx',hy,hxy⟩ := hLink i j hne
    exact ⟨y,hy,(F.singles_same_middle hx hx' hz hy hik hne he hxz hxy).1⟩

private theorem active_adjacency (hLink : ∀ i j, i ≠ j → F.Link i j)
    {i j k : I} {x y : V} (hx : F.Active i x) (hy : F.Active j y) (ij : i ≠ j) (ik : i ≠ k)
    (jk : j ≠ k) : G.Adj x y := by
  obtain ⟨z,hz,hxz⟩ := F.active_meets hLink hx ik
  obtain ⟨z',hz',hyz⟩ := F.active_meets hLink hy jk
  exact (F.singles_same_middle hz hz' hx.1 hy.1 ik.symm jk.symm ij hxz.symm hyz.symm).2.2

private theorem fourth_label [Fintype I] (hCard : 3 < Fintype.card I) (a b c : I) :
    ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  classical
  let S : Finset I := {a,b,c}
  have hS : S.card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (by simp)))
  obtain ⟨d,_,hd⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show S.card < (Finset.univ : Finset I).card by simp only [Finset.card_univ]; omega)
  exact ⟨d,fun he => hd (by simp [S,he]),fun he => hd (by simp [S,he]),fun he => hd (by simp [S,he])⟩

def doubleGraph : SimpleGraph I where
  Adj := F.Double
  symm := fun _ _ => F.double_symm
  loopless := fun _ h => F.double_ne h rfl

private theorem double_connected (hc : G.Connected) {a b : I} (hD : F.Double a b) :
    F.doubleGraph.Connected := by
  let T : Set I := {z | F.doubleGraph.Reachable a z}
  have inc (i : I) (hi : i ∈ T) : ∃ j, F.Double i j := by
    obtain ⟨w⟩ := hi.symm
    cases w with
    | nil => exact ⟨b,hD⟩
    | cons he _ => exact ⟨_,he⟩
  have all := F.label_cut hc T (by
    intro i hi j hj he
    exact hj (hi.trans (SimpleGraph.Adj.reachable (G := F.doubleGraph) he))) (by
    intro i hi j hj he
    obtain ⟨k,hk⟩ := inc i hi
    have eq := F.incident_double_blocks_link hk he
    exact hj (hi.trans (SimpleGraph.Adj.reachable (G := F.doubleGraph) (eq.symm ▸ hk))))
    a Reachable.rfl
  haveI : Nonempty I := ⟨a⟩
  exact ⟨fun x y => (all x).symm.trans (all y)⟩

private theorem double_star [Fintype I] (hc : G.Connected) (hCard : 3 < Fintype.card I)
    {a b : I} (hD : F.Double a b) :
    ∃ h : I, (∀ i, i ≠ h → F.Double h i) ∧ (∀ i j, F.Double i j → i = h ∨ j = h) := by
  classical
  have hConn := F.double_connected hc hD
  obtain ⟨w,hwa,hwb,_⟩ := fourth_label hCard a b b
  obtain ⟨x,hx,y,hy,hxy⟩ := graph_cut hConn ({a,b} : Set I) (by simp : a ∈ ({a,b} : Set I))
    (by simp [hwa,hwb] : w ∉ ({a,b} : Set I))
  have hyA : y ≠ a := fun h => hy (by simp [h])
  have hyB : y ≠ b := fun h => hy (by simp [h])
  have htwo : ∃ h p q : I, F.Double h p ∧ F.Double h q ∧ p ≠ q := by
    rcases (show x = a ∨ x = b by simpa using hx) with he | he
    · exact ⟨a,b,y,hD,he ▸ hxy,hyB.symm⟩
    · exact ⟨b,a,y,F.double_symm hD,he ▸ hxy,hyA.symm⟩
  obtain ⟨h,p,q,hp,hq,hpq⟩ := htwo
  obtain ⟨w',hwh,hwp,hwq⟩ := fourth_label hCard h p q
  obtain ⟨x',hx',r,hr,hxr⟩ := graph_cut hConn ({h,p,q} : Set I)
    (by simp : h ∈ ({h,p,q} : Set I)) (by simp [hwh,hwp,hwq] : w' ∉ ({h,p,q} : Set I))
  have hrh : r ≠ h := fun e => hr (by simp [e])
  have hrp : r ≠ p := fun e => hr (by simp [e])
  have hrq : r ≠ q := fun e => hr (by simp [e])
  have dr : F.Double h r := by
    rcases (show x' = h ∨ x' = p ∨ x' = q by simpa using hx') with rfl | rfl | rfl
    · exact hxr
    · exact (F.double_no_path_three (F.double_symm hq) hp hxr hpq.symm hrq.symm hrh.symm).elim
    · exact (F.double_no_path_three (F.double_symm hp) hq hxr hpq hrp.symm hrh.symm).elim
  let T : Set I := {i | i = h ∨ F.Double h i}
  have all : ∀ i, i ∈ T := by
    intro u
    by_cases hn : u ∈ T
    · exact hn
    exfalso
    obtain ⟨s,hs,t,ht,hst⟩ := graph_cut hConn T (show h ∈ T from Or.inl rfl) hn
    have hth : t ≠ h := fun he => ht (Or.inl he)
    rcases hs with rfl | hds
    · exact ht (Or.inr hst)
    · have hsne : s ≠ h := (F.double_ne hds).symm
      by_cases ep : p = s
      · exact F.double_no_path_three (F.double_symm hq) hds hst
          (fun e => hpq (ep.trans e.symm)) (fun e => ht (Or.inr (e ▸ hq))) hth.symm
      · exact F.double_no_path_three (F.double_symm hp) hds hst ep
          (fun e => ht (Or.inr (e ▸ hp))) hth.symm
  refine ⟨h,fun i hi => (all i).resolve_left hi,?_⟩
  intro i j hij
  by_cases hi : i = h
  · exact Or.inl hi
  by_cases hj : j = h
  · exact Or.inr hj
  have hdi := (all i).resolve_left hi
  have he : ∃ t, F.Double h t ∧ t ≠ i ∧ t ≠ j := by
    by_cases epi : p = i
    · by_cases eqj : q = j
      · exact ⟨r,dr,fun e => hrp (e.trans epi.symm),fun e => hrq (e.trans eqj.symm)⟩
      · exact ⟨q,hq,fun e => hpq (epi.trans e.symm),eqj⟩
    · by_cases epj : p = j
      · by_cases eqi : q = i
        · exact ⟨r,dr,fun e => hrq (e.trans eqi.symm),fun e => hrp (e.trans epj.symm)⟩
        · exact ⟨q,hq,eqi,fun e => hpq (epj.trans e.symm)⟩
      · exact ⟨p,hp,epi,epj⟩
  obtain ⟨t,hd,hti,htj⟩ := he
  exact (F.double_no_path_three (F.double_symm hd) hdi hij hti htj (Ne.symm (show j ≠ h from hj))).elim

private theorem star_has_no_link [Fintype I] (hCard : 3 < Fintype.card I)
    (h : I) (hd : ∀ i, i ≠ h → F.Double h i) {i j : I} (he : F.Link i j) : False := by
  have hn : i ≠ j := he.1
  by_cases hh : i = h
  · subst i
    obtain ⟨k,hk,hkj,_⟩ := fourth_label hCard h j j
    exact hkj (F.incident_double_blocks_link (hd k hk) he).symm
  · have hj := F.incident_double_blocks_link (F.double_symm (hd i hh)) he
    subst j
    obtain ⟨k,hk,hki,_⟩ := fourth_label hCard h i i
    exact hki (F.incident_double_blocks_link (hd k hk) (F.link_symm he)).symm

private def CliqueOn (G : SimpleGraph V) (A : Set V) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ A → x ≠ y → G.Adj x y

private theorem clique_ends [Fintype V] {A : Set V} (hc : CliqueOn G A)
    {a b : V} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
    ∃ p : PathOn G A, p.first = a ∧ p.last = b := by
  classical
  let C := A \ ({a,b} : Set V)
  have hC (x : V) (hx : x ∈ C) : x ≠ a ∧ x ≠ b := by
    have hm := hx.2
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using hm
  obtain ⟨p,hf,hl⟩ := PathOn.clique_between C hne (fun h => (hC a h).1 rfl)
    (fun h => (hC b h).2 rfl) (fun _ => hc ha hb hne)
    (fun ⦃x y⦄ hx hy hn => hc hx.1 hy.1 hn)
    (fun x hx => ⟨hc ha hx.1 (hC x hx).1.symm,hc hx.1 hb (hC x hx).2⟩)
  have hSet : {a,b} ∪ C = A := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases Set.mem_insert_iff.mp hx with rfl | rfl
        · exact ha
        · exact hb
      · exact hx.1
    · intro hx
      by_cases he : x ∈ ({a,b} : Set V)
      · exact Or.inl he
      · exact Or.inr ⟨hx,he⟩
  exact ⟨p.cast hSet,hf,hl⟩

private theorem clique_start [Fintype V] {A : Set V} (hc : CliqueOn G A)
    {a : V} (ha : a ∈ A) : ∃ p : PathOn G A, p.first = a := by
  classical
  by_cases hs : ∃ b ∈ A, b ≠ a
  · obtain ⟨b,hb,hne⟩ := hs
    obtain ⟨p,hf,_⟩ := clique_ends hc ha hb hne.symm
    exact ⟨p,hf⟩
  · have hEq : ({a} : Set V) = A := by
      ext x
      constructor
      · rintro rfl
        exact ha
      · intro hx
        by_contra he
        exact hs ⟨x,hx,he⟩
    exact ⟨(PathOn.singleton a).cast hEq,rfl⟩

private theorem cut_delete [Fintype V] (hk : ConnectivityAtLeast G 2)
    (A : Set V) {x y z : V} (hx : x ∈ A) (hy : y ∉ A) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a ∈ A, ∃ b ∉ A, a ≠ z ∧ b ≠ z ∧ G.Adj a b := by
  classical
  let S : Finset V := {z}
  let T : Set V := (↑S : Set V)ᶜ
  have hc : (G.induce T).Connected := hk.2 S (by simp [S])
  have hX : x ∈ T := by simpa [T,S] using hxz
  have hY : y ∈ T := by simpa [T,S] using hyz
  obtain ⟨a,ha,b,hb,he⟩ := graph_cut hc {v : T | v.val ∈ A}
    (show (⟨x,hX⟩ : T) ∈ {v : T | v.val ∈ A} from hx)
    (show (⟨y,hY⟩ : T) ∉ {v : T | v.val ∈ A} from hy)
  exact ⟨a.val,ha,b.val,hb,by simpa [T,S] using a.property,
    by simpa [T,S] using b.property,he⟩

private theorem clique_module [Fintype V] (hc : G.Connected) (hk : ConnectivityAtLeast G 2)
    {S T : Set V} (hd : Disjoint S T) (hS : CliqueOn G S) (hT : CliqueOn G T)
    {s h : V} (hs : s ∈ S) (hhS : h ∉ S) (hhT : h ∉ T)
    (port : ∀ ⦃a b⦄, a ∈ S → b ∉ S → G.Adj a b → b ∈ T) :
    ∃ p : PathOn G (S ∪ T), p.first ∈ T ∧ p.last ∈ T := by
  classical
  obtain ⟨a,ha,b,hb0,hab⟩ := graph_cut hc S hs hhS
  have hb := port ha hb0 hab
  obtain ⟨c,hcS,d,hd0,_,hdb,hcd⟩ := cut_delete hk S (x := a) (y := h) (z := b) ha hhS
    (fun he => hb0 (he ▸ ha)) (fun he => hhT (he.symm ▸ hb))
  have hdT := port hcS hd0 hcd
  have connectedEnds : ∃ b₁ ∈ T, ∃ b₂ ∈ T, b₁ ≠ b₂ ∧
      ∃ p : PathOn G S, G.Adj b₁ p.first ∧ G.Adj p.last b₂ := by
    by_cases hcA : c = a
    · by_cases hMore : ∃ a' ∈ S, a' ≠ a
      · obtain ⟨w,hw,hwne⟩ := hMore
        obtain ⟨a',ha',b',hb'0,hne,_,he⟩ := cut_delete hk S hw hhS hwne
          (fun e => hhS (e.symm ▸ ha))
        have hb' := port ha' hb'0 he
        by_cases eq : b' = b
        · obtain ⟨p,hf,hl⟩ := clique_ends hS ha' ha hne
          have e₁ : G.Adj b p.first := by rw [hf,← eq]; exact he.symm
          have e₂ : G.Adj p.last d := by rw [hl,← hcA]; exact hcd
          exact ⟨b,hb,d,hdT,hdb.symm,p,e₁,e₂⟩
        · obtain ⟨p,hf,hl⟩ := clique_ends hS ha ha' hne.symm
          exact ⟨b,hb,b',hb',Ne.symm (show b' ≠ b from eq),p,by rw [hf]; exact hab.symm,by rw [hl]; exact he⟩
      · have hEq : ({a} : Set V) = S := by
          ext x
          constructor
          · rintro rfl
            exact ha
          · intro hx
            apply Classical.byContradiction
            intro hn
            exact hMore ⟨x,hx,hn⟩
        exact ⟨b,hb,d,hdT,hdb.symm,(PathOn.singleton a).cast hEq,hab.symm,hcA ▸ hcd⟩
    · obtain ⟨p,hf,hl⟩ := clique_ends hS ha hcS (Ne.symm (show c ≠ a from hcA))
      exact ⟨b,hb,d,hdT,hdb.symm,p,by rw [hf]; exact hab.symm,by rw [hl]; exact hcd⟩
  obtain ⟨b₁,hb₁,b₂,hb₂,hne,p,e₁,e₂⟩ := connectedEnds
  let X := T \ ({b₂} : Set V)
  have hBX : b₁ ∈ X := ⟨hb₁,hne⟩
  obtain ⟨q,hq⟩ := clique_start (A := X) (fun ⦃_ _⦄ ha hb hn => hT ha.1 hb.1 hn) hBX
  have hqS : Disjoint X S := hd.symm.mono_left (fun _ h => h.1)
  let z := q.reverse.join p hqS (by simpa [hq] using e₁)
  have d₂ : Disjoint (X ∪ S) ({b₂} : Set V) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx he
    have he' : x = b₂ := he
    subst x
    rcases hx with hx | hx
    · exact hx.2 rfl
    · exact Set.disjoint_left.mp hd hx hb₂
  let zz := z.join (PathOn.singleton b₂) d₂ (by simpa [z] using e₂)
  have hSet : (X ∪ S) ∪ {b₂} = S ∪ T := by
    ext x
    by_cases he : x = b₂ <;> simp [X,Set.mem_diff,he,hb₂,or_comm]
  exact ⟨zz.cast hSet,by simpa [zz,z] using (show q.last ∈ T from q.last_mem.1),by simpa [zz] using hb₂⟩

private def singleRegion (i : I) : Set V := {x | F.One i x}
private def arms (h i : I) : Set V := {x | F.Two h i x}

private theorem single_regions_disjoint {i j : I} (hne : i ≠ j) :
    Disjoint (F.singleRegion i) (F.singleRegion j) :=
  Set.disjoint_left.mpr (fun _ hx hy => F.one_ne_of_labels hx hy hne rfl)

private theorem base_not_active (i : I) : ¬ F.Active i (F.s i) := by
  rintro ⟨_,j,y,hij,hy,he⟩
  exact F.one_other hy hij (Or.inr he)

private theorem single_path_blocks [Fintype V] [Fintype I] (hc : G.Connected)
    (hk : ConnectivityAtLeast G 2) (hCard : 3 < Fintype.card I) (hD : ∀ i j, ¬ F.Double i j) :
    Traceable G := by
  classical
  have hLink (i j : I) (hne : i ≠ j) := F.link_complete hc hD hne
  have one (x : V) : ∃ i, F.One i x := by
    rcases F.either_one_or_two x with h | ⟨i,j,h⟩
    · exact h
    · exact (hD i j ⟨_,h⟩).elim
  let R := F.singleRegion
  let E (i : I) : Set V := {x | F.Active i x}
  have hp (i : I) : ∃ p : PathOn G (R i), p.first ∈ E i ∧ p.last ∈ E i := by
    obtain ⟨j,hji,_,_⟩ := fourth_label hCard i i i
    obtain ⟨_,a,b,ha,hb,e⟩ := hLink i j hji.symm
    have ae : F.Active i a := ⟨ha,j,b,hji.symm,hb,e⟩
    have hsi : F.s i ∈ R i := F.one_s i
    have hsj : F.s j ∉ R i := fun h => hji (F.has_s h.1)
    have hn : F.s i ≠ a := fun h => F.base_not_active i (h.symm ▸ ae)
    have hn' : F.s j ≠ a := (F.one_ne_s ha hji.symm).symm
    obtain ⟨a',ha',b',hb',hnea,_,he⟩ := cut_delete hk (R i) hsi hsj hn hn'
    obtain ⟨k,hk'⟩ := one b'
    have hki : k ≠ i := fun h => hb' (h ▸ hk')
    have he' : F.Active i a' := ⟨ha',k,b',hki.symm,hk',he⟩
    obtain ⟨p,hf,hl⟩ := clique_ends (A := R i) (F.clique i) ha ha' hnea.symm
    exact ⟨p,hf.symm ▸ ae,hl.symm ▸ he'⟩
  have hd (i j : I) (hne : i ≠ j) : Disjoint (R i) (R j) :=
    F.single_regions_disjoint hne
  have he (i j : I) (hne : i ≠ j) : CompleteBetween G (E i) (E j) := by
    intro x y hx hy
    obtain ⟨k,hki,hkj,_⟩ := fourth_label hCard i j j
    exact F.active_adjacency hLink hx hy hne hki.symm hkj.symm
  have hN : (Finset.univ : Finset I).Nonempty := Finset.card_pos.mp (by simp; omega)
  obtain ⟨p,_,_⟩ := join_path_blocks R E hp hd he (Finset.univ : Finset I) hN
  have hAll : {x | ∃ i ∈ (Finset.univ : Finset I), x ∈ R i} = (Set.univ : Set V) := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := one x
    exact ⟨i,Finset.mem_univ _,hi⟩
  exact (p.cast hAll).traceable

private theorem star_clique [Fintype I] (hCard : 3 < Fintype.card I) (h : I)
    (hd : ∀ i, i ≠ h → F.Double h i)
    {i j : I} {x y : V} (hx : F.Two h i x) (hy : F.Two h j y) (hn : x ≠ y) :
    G.Adj x y := by
  classical
  by_cases he : i = j
  · subst j
    by_contra hxy
    obtain ⟨k,hkh,hki,_⟩ := fourth_label hCard h i i
    obtain ⟨z,hz⟩ := hd k hkh
    exact forbidClaw F.claw (F.adjacent_pairs (F.two_symm hx) hz hki.symm).symm
      (F.adjacent_pairs (F.two_symm hy) hz hki.symm).symm (F.two_edges hz).2.symm
      hn (F.two_outside hx) (F.two_outside hy) hxy
      (fun he => F.two_miss hx hkh hki (Or.inr he.symm))
      (fun he => F.two_miss hy hkh hki (Or.inr he.symm))
  · exact F.adjacent_pairs (F.two_symm hx) hy he

private theorem star_path_blocks [Fintype V] [Fintype I] (hc : G.Connected)
    (hk : ConnectivityAtLeast G 2) (hCard : 3 < Fintype.card I) (h : I)
    (hd : ∀ i, i ≠ h → F.Double h i) (hs : ∀ i j, F.Double i j → i = h ∨ j = h) :
    Traceable G := by
  classical
  let L := {i : I // i ≠ h}
  let R (i : L) := F.singleRegion i.val ∪ F.arms h i.val
  let E (i : L) := F.arms h i.val
  let C := F.singleRegion h
  have ha (i : L) : CliqueOn G (E i) := fun ⦃x y⦄ hx hy hn => F.star_clique hCard h hd hx hy hn
  have noSingleCross {i j : I} (hn : i ≠ j) {x y : V} (hx : F.One i x) (hy : F.One j y)
      (he : G.Adj x y) : False := F.star_has_no_link hCard h hd ⟨hn,x,y,hx,hy,he⟩
  have either (x : V) : (∃ i : I, F.One i x) ∨ ∃ i : L, F.Two h i.val x := by
    rcases F.either_one_or_two x with h | ⟨i,j,ht⟩
    · exact Or.inl h
    · rcases hs i j ⟨_,ht⟩ with he | he
      · subst i
        exact Or.inr ⟨⟨j,ht.1.symm⟩,ht⟩
      · subst j
        exact Or.inr ⟨⟨i,ht.1⟩,F.two_symm ht⟩
  have hw (i : L) (a b : V) (ha : a ∈ F.singleRegion i.val) (hb : b ∉ F.singleRegion i.val)
      (he : G.Adj a b) : b ∈ E i := by
    rcases either b with ⟨j,hj⟩ | ⟨j,hj⟩
    · have hne : i.val ≠ j := fun e => hb (e.symm ▸ hj)
      exact (noSingleCross hne ha hj he).elim
    · by_cases eq : i = j
      · exact eq.symm ▸ hj
      · have ne : (i : I) ≠ (j : I) := fun e => eq (Subtype.ext e)
        exact (F.not_adj_to_two_other hj (F.one_other ha i.property.symm)
          (F.one_other ha ne.symm) he.symm).elim
  have single_arm (i : I) (j : L) :
      Disjoint (F.singleRegion i) (E j) :=
    Set.disjoint_left.mpr (fun _ hx hy => F.one_ne_two hx hy rfl)
  have arms_disj (i j : L) (hne : i ≠ j) : Disjoint (E i) (E j) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have ne : (i : I) ≠ (j : I) := fun e => hne (Subtype.ext e)
    exact F.two_miss hx j.property ne.symm hy.2.2
  have hp (i : L) : ∃ p : PathOn G (R i), p.first ∈ E i ∧ p.last ∈ E i := by
    have hns : F.s h ∉ F.singleRegion i.val := fun he => i.property (F.has_s he.1).symm
    have hnt : F.s h ∉ E i := fun he => F.two_outside he rfl
    exact clique_module hc hk (single_arm i.val i) (F.clique i.val) (ha i)
      (F.one_s i.val) hns hnt (fun ⦃a b⦄ ha hb he => hw i a b ha hb he)
  have disj (i j : L) (hne : i ≠ j) : Disjoint (R i) (R j) :=
    Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_right.mpr
        ⟨F.single_regions_disjoint (fun e => hne (Subtype.ext e)),single_arm i.val j⟩,
       Set.disjoint_union_right.mpr ⟨(single_arm j.val i).symm,arms_disj i j hne⟩⟩
  have adj (i j : L) (hne : i ≠ j) : CompleteBetween G (E i) (E j) := by
    intro x y hx hy
    exact F.adjacent_pairs (F.two_symm hx) hy (fun e => hne (Subtype.ext e))
  obtain ⟨j,hj,_,_⟩ := fourth_label hCard h h h
  let U : Set V := {x | ∃ i ∈ (Finset.univ : Finset L), x ∈ R i}
  obtain ⟨q,⟨i,_,hi⟩,_⟩ := join_path_blocks R E hp disj adj (Finset.univ : Finset L)
    ⟨⟨j,hj⟩,Finset.mem_univ _⟩
  obtain ⟨p,hFirst⟩ := clique_start (A := C) (F.clique h) (F.one_s h)
  have hCU : Disjoint C U := by
    refine Set.disjoint_left.mpr fun x hx hu => ?_
    obtain ⟨j,_,hh⟩ := hu
    rcases hh with hh | hh
    · exact F.one_ne_of_labels hx hh j.property.symm rfl
    · exact F.one_ne_two hx hh rfl
  have e : G.Adj p.reverse.last q.first := by
    simpa only [PathOn.last_reverse,hFirst] using (F.two_edges hi).1
  have hAll : C ∪ U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases either x with ⟨i,hi⟩ | ⟨i,hi⟩
    · by_cases he : i = h
      · left
        change F.One h x
        exact he ▸ hi
      · exact Or.inr ⟨⟨i,he⟩,Finset.mem_univ _,Or.inl hi⟩
    · exact Or.inr ⟨i,Finset.mem_univ _,Or.inr hi⟩
  exact ((p.reverse.join q hCU e).cast hAll).traceable

include F in
/-- Traceability from the maximum stable-set constraints, for at least four labels. -/
theorem frame_traceable [Fintype V] [Fintype I] (hc : G.Connected)
    (hk : ConnectivityAtLeast G 2) (hCard : 3 < Fintype.card I) : Traceable G := by
  classical
  by_cases hh : ∃ i j, F.Double i j
  · obtain ⟨i,j,he⟩ := hh
    obtain ⟨h,h1,h2⟩ := F.double_star hc hCard he
    exact F.star_path_blocks hc hk hCard h h1 h2
  · push_neg at hh
    exact F.single_path_blocks hc hk hCard hh

end Frame

private theorem frame_of_independent_four [Fintype V] (hcl : ClawFree G) (ht : NoTree5 G)
    (A : Fin 4 ↪ V) (hA : IndependentFour G A) (hc : G.Connected)
    (hk : ConnectivityAtLeast G 2) : Traceable G := by
  classical
  let ind (S : Finset V) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y
  let sets := (Finset.univ : Finset (Finset V)).filter ind
  let S₀ := (Finset.univ : Finset (Fin 4)).map A
  have hS₀ : S₀ ∈ sets := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro x hx y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hy
    exact hA i j
  obtain ⟨S,hS,hM⟩ := Finset.exists_max_image sets Finset.card ⟨S₀,hS₀⟩
  have hInd := (Finset.mem_filter.mp hS).2
  let I := {x // x ∈ S}
  let s : I ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hCard : 3 < Fintype.card I := by
    have h := hM S₀ hS₀
    rw [Fintype.card_coe]
    simp [S₀] at h
    omega
  have cov (x : V) : ∃ i : I, Touch G s i x := by
    by_cases hx : x ∈ S
    · exact ⟨⟨x,hx⟩,Or.inl rfl⟩
    · by_contra hn
      have hIS : ind (insert x S) := by
        intro a ha b hb he
        rcases Finset.mem_insert.mp ha with ha | ha <;> rcases Finset.mem_insert.mp hb with hb | hb
        · exact he.ne (ha.trans hb.symm)
        · rw [ha] at he
          exact hn ⟨⟨_,hb⟩,Or.inr he.symm⟩
        · rw [hb] at he
          exact hn ⟨⟨_,ha⟩,Or.inr he⟩
        · exact hInd _ ha _ hb he
      have hm := hM (insert x S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hIS⟩)
      rw [Finset.card_insert_of_not_mem hx] at hm
      omega
  have cq (i : I) : ∀ ⦃x y⦄, Single G s i x → Single G s i y → x ≠ y → G.Adj x y := by
    intro x y hx hy hn
    by_cases e : G.Adj x y
    · exact e
    exfalso
    let R := S.erase (s i)
    have noTouch (a : V) (ha : a ∈ R) (v : V) (hv : Single G s i v) :
        ¬ Touch G s ⟨a,(Finset.mem_erase.mp ha).2⟩ v := by
      intro h
      exact (Finset.mem_erase.mp ha).1 (congrArg Subtype.val (hv.2 _ h))
    have nxy (v : V) (hv : Single G s i v) : v ∉ R := fun he => noTouch v he v hv (Or.inl rfl)
    have hIS : ind (insert x (insert y R)) := by
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
      · exact hab.ne (ha.trans hb.symm)
      · rw [ha,hb] at hab
        exact e hab
      · rw [ha] at hab
        exact noTouch _ hb x hx (Or.inr hab.symm)
      · rw [ha,hb] at hab
        exact e hab.symm
      · exact hab.ne (ha.trans hb.symm)
      · rw [ha] at hab
        exact noTouch _ hb y hy (Or.inr hab.symm)
      · rw [hb] at hab
        exact noTouch _ ha x hx (Or.inr hab)
      · rw [hb] at hab
        exact noTouch _ ha y hy (Or.inr hab)
      · exact hInd _ (Finset.mem_erase.mp ha).2 _ (Finset.mem_erase.mp hb).2 hab
    have hm := hM _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hIS⟩)
    rw [Finset.card_insert_of_not_mem (by simp [hn,nxy x hx]),
      Finset.card_insert_of_not_mem (nxy y hy)] at hm
    have hR : R.card = S.card - 1 := Finset.card_erase_of_mem i.property
    omega
  let F : Frame G I := ⟨s,fun i j => hInd _ i.property _ j.property,cov,cq,hcl,ht⟩
  exact F.frame_traceable hc hk hCard

/-- The claw-free branch uses only the absence of an induced five-vertex path. -/
theorem claw_free_traceable [Fintype V] (hc : G.Connected) (hk : ConnectivityAtLeast G 2)
    (ht : treeNumber G ≤ 4) (hcl : ClawFree G) : Traceable G := by
  classical
  by_cases ha : ∃ I, IndependentFour G I
  · obtain ⟨I,e⟩ := ha
    exact frame_of_independent_four hcl (noTree5_of_treeNumber_le_four ht) I e hc hk
  · push_neg at ha
    exact traceable_of_no_independent_four hc hk ha

end ClawFreeCase

/-- The exact Graffiti.pc #199 implication at vertex connectivity two. -/
theorem conjecture199_connectivity_two {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hc : G.Connected) (hk : vertexConnectivity G = 2)
    (ht : treeNumber G ≤ 4) : Traceable G := by
  classical
  by_cases hcl : ∃ Q, IsClaw G Q
  · exact conjecture199_connectivity_two_of_induced_claw hc hk ht hcl
  · push_neg at hcl
    exact ClawFreeCase.claw_free_traceable hc
      (hk ▸ connectivityAtLeast_vertexConnectivity G) ht hcl

#print axioms ClawFreeCase.Frame.frame_traceable
#print axioms ClawFreeCase.claw_free_traceable
#print axioms conjecture199_connectivity_two

end Graffiti199K2


namespace Graffiti199K2
namespace LowConnectivity
open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- A finite induced tree can be certified by a rank with one descending
neighbor at each vertex other than the root. -/
theorem induced_rank_lower_bound [Fintype V] [Fintype W] (f : W ↪ V) (r : W)
    (rank : W → ℕ)
    (hne : ∀ ⦃x y⦄, G.Adj (f x) (f y) → rank x ≠ rank y)
    (hr : ∀ ⦃x⦄, ¬ (G.Adj (f r) (f x) ∧ rank x < rank r))
    (hp : ∀ x, x ≠ r → ∃! y, G.Adj (f x) (f y) ∧ rank y < rank x) :
    Fintype.card W ≤ treeNumber G := by
  classical
  let S := (Finset.univ : Finset W).map f
  let e (x : W) : (↑S : Set V) := ⟨f x,Finset.mem_map.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩
  have inj : Function.Injective e := fun _ _ h => f.injective (congrArg Subtype.val h)
  have surj : Function.Surjective e := by
    intro v
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp v.property
    exact ⟨x,Subtype.ext hx⟩
  let E := Equiv.ofBijective e ⟨inj,surj⟩
  let ρ (v : (↑S : Set V)) := rank (E.symm v)
  have eRank (x : W) : ρ (e x) = rank x := congrArg rank (E.symm_apply_apply x)
  have ht : (G.induce (↑S : Set V)).IsTree := by
    apply tree_of_rank (e r) ρ
    · intro x y he
      obtain ⟨x,rfl⟩ := surj x
      obtain ⟨y,rfl⟩ := surj y
      rw [eRank,eRank]
      exact hne he
    · intro x he
      obtain ⟨x,rfl⟩ := surj x
      rw [eRank,eRank] at he
      exact hr he
    · intro x hx
      obtain ⟨x,rfl⟩ := surj x
      obtain ⟨y,hY,hU⟩ := hp x (fun h => hx (congrArg e h))
      refine ⟨e y,⟨hY.1,by simpa only [eRank] using hY.2⟩,?_⟩
      intro z hz
      obtain ⟨z,rfl⟩ := surj z
      exact congrArg e (hU z ⟨hz.1,by simpa only [eRank] using hz.2⟩)
  simpa [S] using card_le_treeNumber S ht

/-- An independent set of neighbors yields an induced star. -/
theorem independent_neighbors_tree_bound [Fintype V] {n : ℕ} (c : V)
    (f : Fin n ↪ V) (ha : ∀ i, G.Adj c (f i)) (hi : ∀ i j, ¬G.Adj (f i) (f j)) :
    n + 1 ≤ treeNumber G := by
  let s : Fin (n+1) → V := Fin.cons c f
  have inj : Function.Injective s := by
    intro x
    refine Fin.cases (motive := fun x => ∀ y, s x = s y → x = y) ?_ ?_ x
    · intro y
      refine Fin.cases ?_ ?_ y
      · intro _; rfl
      · intro j h; exact ((ha j).ne h).elim
    · intro i y
      refine Fin.cases ?_ ?_ y
      · intro h; exact ((ha i).ne h.symm).elim
      · intro j h; exact congrArg Fin.succ (f.injective h)
  let E : Fin (n+1) ↪ V := ⟨s,inj⟩
  have H : Fintype.card (Fin (n+1)) ≤ treeNumber G := by
    apply induced_rank_lower_bound E 0 Fin.val
    · intro x y h e
      exact h.ne (congrArg E (Fin.ext e))
    · intro x hx
      exact Nat.not_lt_zero _ hx.2
    · intro x hx
      refine Fin.cases ?_ ?_ x hx
      · intro h; exact (h rfl).elim
      · intro j _
        refine ⟨0,⟨(ha j).symm,Nat.zero_lt_succ _⟩,?_⟩
        intro k hk
        refine Fin.cases ?_ ?_ k hk
        · intro _; rfl
        · intro i he; exact (hi j i he.1).elim
  simpa using H

private theorem claw_bound [Fintype V] {c a b d : V}
    (ha : G.Adj c a) (hb : G.Adj c b) (hd : G.Adj c d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (nab : ¬G.Adj a b) (nad : ¬G.Adj a d) (nbd : ¬G.Adj b d) : 4 ≤ treeNumber G := by
  let f : Fin 3 → V := ![a,b,d]
  have hi : Function.Injective f := List.nodup_ofFn.mp (show [a,b,d].Nodup by simp [hab,had,hbd])
  refine independent_neighbors_tree_bound c ⟨f,hi⟩ ?_ ?_
  · intro i
    fin_cases i <;> assumption
  · intro i j
    have nba : ¬G.Adj b a := fun h => nab h.symm
    have nda : ¬G.Adj d a := fun h => nad h.symm
    have ndb : ¬G.Adj d b := fun h => nbd h.symm
    fin_cases i <;> fin_cases j <;> simp [f,nab,nad,nbd,nba,nda,ndb]

private theorem path4_bound [Fintype V] {a b c d : V}
    (hN : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (nac : ¬G.Adj a c) (nad : ¬G.Adj a d) (nbd : ¬G.Adj b d) : 4 ≤ treeNumber G := by
  let f : Fin 4 → V := ![a,b,c,d]
  let E : Fin 4 ↪ V := ⟨f,List.nodup_ofFn.mp (show (List.ofFn f).Nodup from hN)⟩
  have ne : ∀ i j : Fin 4, G.Adj (E i) (E j) ↔
      min i.val j.val + 1 = max i.val j.val := by
    have nca : ¬G.Adj c a := fun h => nac h.symm
    have nda : ¬G.Adj d a := fun h => nad h.symm
    have ndb : ¬G.Adj d b := fun h => nbd h.symm
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f,E,hab,hbc,hcd,hab.symm,hbc.symm,hcd.symm,nac,nad,nbd,nca,nda,ndb]
  have h : Fintype.card (Fin 4) ≤ treeNumber G := by
    apply induced_rank_lower_bound E 0 Fin.val
    · intro i j ha hEq
      exact ha.ne (congrArg E (Fin.ext hEq))
    · intro i hi
      exact Nat.not_lt_zero _ hi.2
    · intro i hi
      simp only [ne]
      have h : ∀ i : Fin 4, i ≠ 0 → ∃! j : Fin 4,
          min i.val j.val + 1 = max i.val j.val ∧ j.val < i.val := by
        unfold ExistsUnique
        decide
      exact h i hi
  simpa using h

theorem graph_cut {U : Type*} {H : SimpleGraph U} (hc : H.Connected)
    (A : Set U) {x y : U} (hx : x ∈ A) (hy : y ∉ A) :
    ∃ a ∈ A, ∃ b ∉ A, H.Adj a b := by
  classical
  obtain ⟨p⟩ := hc x y
  induction p with
  | nil => exact (hy hx).elim
  | @cons a b c e _ ih =>
    by_cases hn : b ∈ A
    · exact ih hn hy
    · exact ⟨a,hx,b,hn,e⟩

private theorem connAtLeast_le [Fintype V] {k : ℕ} (h : ConnectivityAtLeast G k) :
    k ≤ vertexConnectivity G := by
  classical
  unfold vertexConnectivity
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1,h⟩)

private theorem small_connected_traceable [Fintype V] (hc : G.Connected)
    (hk : ConnectivityAtLeast G 1) (hn : Fintype.card V ≤ 2) : Traceable G := by
  classical
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have compl : ∀ ⦃a b : V⦄, a ≠ b → G.Adj a b := by
    intro a b hab
    have hpos := min_degree_of_connectivityAtLeast hk a
    obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset a).card by omega)
    have he := (G.mem_neighborFinset a c).mp hc
    by_cases eq : c = b
    · exact eq ▸ he
    · have n3 : ({a,b,c} : Finset V).card = 3 := by
        simp [hab,he.ne,Ne.symm (show c ≠ b from eq)]
      have hle := Finset.card_le_univ ({a,b,c} : Finset V)
      omega
  have pp := PathOn.ofClique (A := (Set.univ : Set V))
    (by obtain ⟨v⟩ := hc.nonempty; exact ⟨v,Set.mem_univ _⟩)
    (fun ⦃a b⦄ _ _ h => compl h)
  exact pp.traceable

private theorem cut_one_exists [Fintype V] [Nonempty V] (hconn : vertexConnectivity G = 1)
    (hord : 2 < Fintype.card V) :
    ∃ v : V, ¬ (G.induce {x | x ≠ v}).Connected := by
  classical
  have h1 : ConnectivityAtLeast G 1 := hconn ▸ connectivityAtLeast_vertexConnectivity G
  have h2 : ¬ ConnectivityAtLeast G 2 := by
    intro h
    have hle := connAtLeast_le h
    omega
  have hbad : ∃ S : Finset V, S.card < 2 ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected := by
    by_contra! h
    exact h2 ⟨hord,h⟩
  obtain ⟨S,hs,hd⟩ := hbad
  have hcard : S.card = 1 := by
    by_contra he
    exact hd (h1.2 S (by omega))
  obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hcard
  have heq : ((↑({v} : Finset V) : Set V)ᶜ) = {x | x ≠ v} := by ext; simp
  exact ⟨v,heq ▸ hd⟩

/-- If deleting one vertex disconnects the graph, each component touches it. -/
private theorem neighbor_in_component (hc : G.Connected) (v : V)
    (x : {z // z ∈ ({z : V | z ≠ v} : Set V)}) :
    ∃ y : {z // z ∈ ({z : V | z ≠ v} : Set V)},
      (G.induce {z | z ≠ v}).Reachable x y ∧ G.Adj v y.val := by
  let H := G.induce {z | z ≠ v}
  let A : Set V := {z | ∃ hz : z ≠ v, H.Reachable x ⟨z,hz⟩}
  have hx : x.val ∈ A := ⟨x.property,Reachable.rfl⟩
  have hv : v ∉ A := fun h => h.1 rfl
  obtain ⟨a,ha,b,hb,e⟩ := graph_cut hc A hx hv
  obtain ⟨ha',ha⟩ := ha
  have hbv : b = v := by
    by_contra hne
    exact hb ⟨hne,ha.trans (SimpleGraph.Adj.reachable (G := H) e)⟩
  exact ⟨⟨a,ha'⟩,ha,hbv ▸ e.symm⟩

private theorem cut_universal [Fintype V] (hc : G.Connected) (ht : treeNumber G ≤ 3)
    (v : V) {x y : {z // z ∈ ({z : V | z ≠ v} : Set V)}}
    (hxy : ¬ (G.induce {z | z ≠ v}).Reachable x y) :
    ∀ z : V, z ≠ v → G.Adj v z := by
  classical
  let H := G.induce {z | z ≠ v}
  intro z hz
  by_contra hn
  let a : {z // z ∈ ({z : V | z ≠ v} : Set V)} := ⟨z,hz⟩
  have opp : ∃ p, ¬ H.Reachable a p := by
    by_cases hax : H.Reachable a x
    · exact ⟨y,fun hay => hxy (hax.symm.trans hay)⟩
    · exact ⟨x,hax⟩
  obtain ⟨p,hp⟩ := opp
  obtain ⟨q,hrq,hvq⟩ := neighbor_in_component hc v a
  obtain ⟨b,hrb,hvb⟩ := neighbor_in_component hc v p
  obtain ⟨w⟩ := hrq
  obtain ⟨u,hu,r,hr,hur⟩ := by
    have aIn : a ∈ {u | H.Reachable a u ∧ ¬G.Adj v u.val} := ⟨Reachable.rfl,hn⟩
    have qOut : q ∉ {u | H.Reachable a u ∧ ¬G.Adj v u.val} := fun h => h.2 hvq
    have aux (A : Set {z // z ∈ ({z : V | z ≠ v} : Set V)}) {j k} (w : H.Walk j k)
        (hj : j ∈ A) (hk : k ∉ A) : ∃ u ∈ A, ∃ r ∉ A, H.Adj u r := by
      induction w with
      | nil => exact (hk hj).elim
      | @cons j z k e _ ih =>
        by_cases h : z ∈ A
        · exact ih h hk
        · exact ⟨j,hj,z,h,e⟩
    exact aux _ w aIn qOut
  have harr : H.Reachable a r := hu.1.trans hur.reachable
  have hvr : G.Adj v r.val := by
    by_contra he
    exact hr ⟨harr,he⟩
  have cross (s : {z // z ∈ ({z : V | z ≠ v} : Set V)}) (hs : H.Reachable a s) :
      s.val ≠ b.val ∧ ¬ G.Adj s.val b.val := by
    constructor
    · intro he
      exact hp ((Subtype.ext he ▸ hs).trans hrb.symm)
    · intro he
      exact hp (hs.trans ((SimpleGraph.Adj.reachable (G := H) he).trans hrb.symm))
  have hNu : [u.val,r.val,v,b.val].Nodup := by
    have e : G.Adj u.val r.val := hur
    have huV : u.val ≠ v := u.property
    have hrV : r.val ≠ v := r.property
    have hbV : b.val ≠ v := b.property
    simp [e.ne,huV,hrV,hbV.symm,(cross u hu.1).1,(cross r harr).1]
  have ht' := path4_bound hNu (show G.Adj u.val r.val from hur) hvr.symm hvb
    (fun he => hu.2 he.symm) (cross u hu.1).2 (cross r harr).2
  omega

private theorem two_clique_sides [Fintype V] (hc : G.Connected)
    (ht : treeNumber G ≤ 3) (ho : 2 < Fintype.card V) (v : V)
    (hn : ¬ (G.induce {z | z ≠ v}).Connected) : Traceable G := by
  classical
  let H := G.induce {z | z ≠ v}
  haveI : Nonempty {z // z ∈ ({z : V | z ≠ v} : Set V)} := by
    obtain ⟨w,_,hw⟩ := Finset.exists_mem_not_mem_of_card_lt_card
      (show ({v} : Finset V).card < (Finset.univ : Finset V).card by simp; omega)
    exact ⟨w,by simpa using hw⟩
  have np : ¬ H.Preconnected := fun h => hn ⟨h⟩
  unfold SimpleGraph.Preconnected at np
  push_neg at np
  obtain ⟨x,y,hxy⟩ := np
  have uv := cut_universal hc ht v hxy
  let A : Set V := {z | ∃ hz : z ≠ v, H.Reachable x ⟨z,hz⟩}
  let B : Set V := {z | z ≠ v ∧ z ∉ A}
  have xa : x.val ∈ A := ⟨x.property,Reachable.rfl⟩
  have yb : y.val ∈ B := ⟨y.property,fun h => hxy h.2⟩
  have cross {a b : V} (ha : a ∈ A) (hb : b ∈ B) : ¬ G.Adj a b := by
    intro e
    exact hb.2 ⟨hb.1,ha.2.trans (SimpleGraph.Adj.reachable (G := H) e)⟩
  have dAB : Disjoint A B := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha)
  have complA : ∀ ⦃a b⦄, a ∈ A → b ∈ A → a ≠ b → G.Adj a b := by
    intro a b ha hb hab
    by_cases he : G.Adj a b
    · exact he
    exfalso
    have hn' := claw_bound (c := v) (a := a) (b := b) (d := y.val)
      (uv a ha.1) (uv b hb.1) (uv y.val yb.1) hab
      (fun e => yb.2 (e ▸ ha)) (fun e => yb.2 (e ▸ hb)) he (cross ha yb) (cross hb yb)
    omega
  have complB : ∀ ⦃a b⦄, a ∈ B → b ∈ B → a ≠ b → G.Adj a b := by
    intro a b ha hb hab
    by_cases he : G.Adj a b
    · exact he
    exfalso
    have hn' := claw_bound (c := v) (a := a) (b := b) (d := x.val)
      (uv a ha.1) (uv b hb.1) (uv x.val xa.1) hab
      (fun e => ha.2 (e.symm ▸ xa)) (fun e => hb.2 (e.symm ▸ xa)) he
      (fun e => cross xa ha e.symm) (fun e => cross xa hb e.symm)
    omega
  let a := PathOn.ofClique ⟨_,xa⟩ complA
  let b := PathOn.ofClique ⟨_,yb⟩ complB
  let av := a.join (PathOn.singleton v)
    (Set.disjoint_singleton_right.mpr (fun h => h.1 rfl)) (uv _ a.last_mem.1).symm
  let avb := av.join b (Set.disjoint_union_left.mpr
    ⟨dAB,Set.disjoint_singleton_left.mpr (fun h => h.1 rfl)⟩)
    (by simpa [av] using uv _ b.first_mem.1)
  have hSet : ((A ∪ {v}) ∪ B) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases h : z = v
    · exact Or.inl (Or.inr h)
    · by_cases he : z ∈ A
      · exact Or.inl (Or.inl he)
      · exact Or.inr ⟨h,he⟩
  exact (avb.cast hSet).traceable

/-- Exact catalogue implication at vertex connectivity one, including K₂. -/
theorem conjecture199_connectivity_one [Fintype V] [Nonempty V] (hc : G.Connected)
    (hk : vertexConnectivity G = 1) (ht : treeNumber G ≤ 3) : Traceable G := by
  classical
  by_cases h : Fintype.card V ≤ 2
  · exact small_connected_traceable hc (hk ▸ connectivityAtLeast_vertexConnectivity G) h
  · obtain ⟨v,hv⟩ := cut_one_exists (G := G) hk (by omega)
    exact two_clique_sides hc ht (by omega) v hv

#print axioms independent_neighbors_tree_bound
#print axioms conjecture199_connectivity_one

end LowConnectivity
end Graffiti199K2


namespace Graffiti199K2
namespace LowConnectivity
open SimpleGraph

variable {V I J : Type*} {G : SimpleGraph V}

theorem independent_neighbors_card_bound [Fintype V] [Fintype I] (c : V) (f : I ↪ V)
    (ha : ∀ i, G.Adj c (f i)) (hi : ∀ i j, ¬G.Adj (f i) (f j)) :
    Fintype.card I + 1 ≤ treeNumber G := by
  classical
  let E := (Fintype.equivFin I).symm.toEmbedding
  exact independent_neighbors_tree_bound c (E.trans f) (fun i => ha (E i))
    (fun i j => hi (E i) (E j))

/-- Count a star and any collection of new vertices each attached to exactly one leaf. -/
theorem rooted_star_bound [Fintype V] [Fintype I] [Fintype J]
    (c : V) (f : I ↪ V) (z : J ↪ V) (branch : J → I) (near : J → Prop)
    (ha : ∀ i, G.Adj c (f i)) (hi : ∀ i j, ¬G.Adj (f i) (f j))
    (hnc : ∀ j, z j ≠ c) (hnf : ∀ i j, z j ≠ f i)
    (hn : ∀ j, G.Adj c (z j) ↔ near j) (hnz : ∀ j k, ¬G.Adj (z j) (z k))
    (hz : ∀ i j, G.Adj (f i) (z j) ↔ i = branch j ∧ ¬ near j) :
    Fintype.card I + Fintype.card J + 1 ≤ treeNumber G := by
  classical
  let v : Option (I ⊕ J) → V
    | none => c
    | some (.inl i) => f i
    | some (.inr j) => z j
  have inj : Function.Injective v := by
    intro a b h
    rcases a with - | (i | i) <;> rcases b with - | (j | j)
    · rfl
    · exact ((ha j).ne h).elim
    · exact (hnc j h.symm).elim
    · exact ((ha i).ne h.symm).elim
    · exact congrArg (fun i => some (Sum.inl i : I ⊕ J)) (f.injective h)
    · exact (hnf i j h.symm).elim
    · exact (hnc i h).elim
    · exact (hnf j i h).elim
    · exact congrArg (fun i => some (Sum.inr i : I ⊕ J)) (z.injective h)
  let ρ : Option (I ⊕ J) → ℕ
    | none => 0
    | some (.inl _) => 1
    | some (.inr _) => 2
  have ht : Fintype.card (Option (I ⊕ J)) ≤ treeNumber G := by
    apply induced_rank_lower_bound (⟨v,inj⟩ : Option (I ⊕ J) ↪ V) none ρ
    · intro a b h
      rcases a with - | (i | i) <;> rcases b with - | (j | j)
      · exact (G.loopless _ h).elim
      · simp [ρ]
      · simp [ρ]
      · simp [ρ]
      · exact (hi i j h).elim
      · simp [ρ]
      · simp [ρ]
      · simp [ρ]
      · exact (hnz i j h).elim
    · intro x h
      exact Nat.not_lt_zero _ h.2
    · intro x hx
      rcases x with - | (i | j)
      · exact (hx rfl).elim
      · refine ⟨none,⟨(ha i).symm,by simp [ρ]⟩,?_⟩
        intro y hy
        rcases y with - | (k | k)
        · rfl
        · exact (hi i k hy.1).elim
        · exact (by decide : ¬(2 : ℕ) < 1) hy.2 |>.elim
      · by_cases he : near j
        · refine ⟨none,⟨((hn j).mpr he).symm,by simp [ρ]⟩,?_⟩
          intro y hy
          rcases y with - | (k | k)
          · rfl
          · exact (((hz k j).mp hy.1.symm).2 he).elim
          · exact (hnz j k hy.1).elim
        · refine ⟨some (.inl (branch j)),⟨((hz _ j).mpr ⟨rfl,he⟩).symm,by simp [ρ]⟩,?_⟩
          intro y hy
          rcases y with - | (k | k)
          · exact (he ((hn j).mp hy.1.symm)).elim
          · exact congrArg (fun k => some (Sum.inl k : I ⊕ J)) ((hz k j).mp hy.1.symm).1
          · exact (hnz j k hy.1).elim
  simpa using ht

theorem extended_star_bound [Fintype V] [Fintype I] [Fintype J]
    (c : V) (f : I ↪ V) (z : J ↪ V) (branch : J → I)
    (ha : ∀ i, G.Adj c (f i)) (hi : ∀ i j, ¬G.Adj (f i) (f j))
    (hnc : ∀ j, z j ≠ c) (hnf : ∀ i j, z j ≠ f i)
    (hn : ∀ j, ¬G.Adj c (z j)) (hnz : ∀ j k, ¬G.Adj (z j) (z k))
    (hz : ∀ i j, G.Adj (f i) (z j) ↔ i = branch j) :
    Fintype.card I + Fintype.card J + 1 ≤ treeNumber G :=
  rooted_star_bound c f z branch (fun _ => False) ha hi hnc hnf
    (fun j => ⟨hn j,False.elim⟩) hnz (fun i j => by simpa using hz i j)

namespace ThreeCut

variable [Fintype V]

abbrev Rem (S : Finset V) := {v : V // v ∉ S}
def Deleted (G : SimpleGraph V) (S : Finset V) := G.induce {v | v ∉ S}
abbrev Comp (G : SimpleGraph V) (S : Finset V) := (Deleted G S).ConnectedComponent

noncomputable def compFintype (G : SimpleGraph V) (S : Finset V) :
    Fintype (Comp G S) := by
  classical
  exact Fintype.ofSurjective (Deleted G S).connectedComponentMk Quot.mk_surjective

def ComponentSet (G : SimpleGraph V) (S : Finset V) (i : Comp G S) : Set V :=
  {x | ∃ hx : x ∉ S, (Deleted G S).connectedComponentMk ⟨x,hx⟩ = i}

omit [Fintype V] in
private theorem comp_eq_of_edge {S : Finset V} {a b : Rem S}
    (he : G.Adj a.val b.val) :
    (Deleted G S).connectedComponentMk a = (Deleted G S).connectedComponentMk b :=
  SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable (G := Deleted G S) he)

/-- Each vertex of a three-vertex cut contacts every deletion component. -/
theorem cut_touches_components (hk : ConnectivityAtLeast G 3) {S : Finset V}
    (hS : S.card = 3) {s : V} (hs : s ∈ S) (i : Comp G S) :
    ∃ x : Rem S, (Deleted G S).connectedComponentMk x = i ∧ G.Adj s x.val := by
  classical
  let H := Deleted G S
  let T := S.erase s
  let X : Set V := (↑T : Set V)ᶜ
  have cardT : T.card < 3 := by simp [T,Finset.card_erase_of_mem hs,hS]
  have hConn : (G.induce X).Connected := hk.2 T cardT
  obtain ⟨w,hw⟩ := i.exists_rep
  have hwX : w.val ∈ X := fun h => w.property (Finset.mem_of_mem_erase h)
  have hsX : s ∈ X := by simp [X,T]
  let A : Set (↑X) := {x | x.val ∈ ComponentSet G S i}
  have hIn : ⟨w.val,hwX⟩ ∈ A := ⟨w.property,hw⟩
  have hOut : ⟨s,hsX⟩ ∉ A := fun he => he.1 hs
  obtain ⟨x,hx,y,hy,he⟩ := graph_cut hConn A hIn hOut
  obtain ⟨hxS,hxi⟩ := hx
  have hyS : y.val ∈ S := by
    by_contra h
    have goe : G.Adj x.val y.val := he
    exact hy ⟨h,(comp_eq_of_edge (S := S) (a := ⟨x.val,hxS⟩)
      (b := ⟨y.val,h⟩) goe).symm.trans hxi⟩
  have hyEq : y.val = s := by
    by_contra he
    exact y.property (Finset.mem_erase.mpr ⟨he,hyS⟩)
  have he' : G.Adj x.val y.val := he
  exact ⟨⟨x.val,hxS⟩,hxi,hyEq ▸ he'.symm⟩

private theorem representatives (hk : ConnectivityAtLeast G 3) {S : Finset V}
    (hS : S.card = 3) {s : V} (hs : s ∈ S) :
    ∃ f : Comp G S ↪ V,
      (∀ i, f i ∈ ComponentSet G S i) ∧ (∀ i, G.Adj s (f i)) := by
  classical
  choose f hlabel he using cut_touches_components hk hS hs
  let emb : Comp G S ↪ V :=
    ⟨fun i => (f i).val,fun i j h => (hlabel i).symm.trans
      ((congrArg _ (Subtype.ext h)).trans (hlabel j))⟩
  exact ⟨emb,fun i => ⟨(f i).property,hlabel i⟩,he⟩

omit [Fintype V] in
private theorem componentSets_disjoint {S : Finset V} {i j : Comp G S} (hne : i ≠ j) :
    Disjoint (ComponentSet G S i) (ComponentSet G S j) := by
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨_,hi⟩ ⟨_,hj⟩
  exact hne (hi.symm.trans hj)

omit [Fintype V] in
private theorem componentSets_no_edges {S : Finset V} {i j : Comp G S} (hne : i ≠ j)
    {x y : V} (hx : x ∈ ComponentSet G S i) (hy : y ∈ ComponentSet G S j) :
    ¬ G.Adj x y := by
  rintro he
  obtain ⟨hx,hi⟩ := hx
  obtain ⟨hy,hj⟩ := hy
  exact hne (hi.symm.trans ((comp_eq_of_edge (S := S) (a := ⟨x,hx⟩) (b := ⟨y,hy⟩) he).trans hj))

/-- The number of components left by a three-cut is at most tree number minus one. -/
theorem component_card_tree_bound (hk : ConnectivityAtLeast G 3) {S : Finset V}
    (hS : S.card = 3) :
    letI := compFintype G S
    Fintype.card (Comp G S) + 1 ≤ treeNumber G := by
  classical
  letI := compFintype G S
  obtain ⟨s,hs⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨f,hf,hn⟩ := representatives hk hS hs
  refine independent_neighbors_card_bound s f hn ?_
  intro i j
  by_cases h : i = j
  · subst j
    exact G.loopless _
  · exact componentSets_no_edges h (hf i) (hf j)

private theorem walk_cut {U : Type*} {H : SimpleGraph U} (A : Set U) {x y : U}
    (p : H.Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ a ∈ A, ∃ b ∉ A, H.Adj a b := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons a b c e _ ih =>
    by_cases h : b ∈ A
    · exact ih h hy
    · exact ⟨a,hx,b,h,e⟩

private theorem near_far_edge (hk : ConnectivityAtLeast G 3) {S : Finset V}
    (hS : S.card = 3) {s : V} (hs : s ∈ S) {i : Comp G S}
    {w : V} (hw : w ∈ ComponentSet G S i) (hn : ¬G.Adj s w) :
    ∃ x ∈ ComponentSet G S i, ∃ y ∈ ComponentSet G S i,
      G.Adj s x ∧ ¬ G.Adj s y ∧ G.Adj x y := by
  classical
  obtain ⟨hwS,hwi⟩ := hw
  obtain ⟨v,hvi,hsv⟩ := cut_touches_components hk hS hs i
  let H := Deleted G S
  let A : Set (Rem S) := {z | H.connectedComponentMk z = i ∧ ¬ G.Adj s z.val}
  have he : H.connectedComponentMk ⟨w,hwS⟩ = H.connectedComponentMk v :=
    hwi.trans hvi.symm
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact he
  obtain ⟨y,hy,x,hx,hxy⟩ := walk_cut A p ⟨hwi,hn⟩ (fun h => h.2 hsv)
  have ez : G.Adj y.val x.val := hxy
  have hxi : H.connectedComponentMk x = i := (comp_eq_of_edge (S := S) (a := y) (b := x) ez).symm.trans hy.1
  have hsa : G.Adj s x.val := by
    by_cases h : G.Adj s x.val
    · exact h
    · exact (hx ⟨hxi,h⟩).elim
  exact ⟨x.val,⟨x.property,hxi⟩,y.val,⟨y.property,hy.1⟩,hsa,hy.2,ez.symm⟩

private theorem representatives_override (hk : ConnectivityAtLeast G 3) {S : Finset V}
    (hS : S.card = 3) {s : V} (hs : s ∈ S) {i : Comp G S}
    {w : V} (hw : w ∈ ComponentSet G S i) (he : G.Adj s w) :
    ∃ f : Comp G S ↪ V, (∀ j, f j ∈ ComponentSet G S j) ∧
      (∀ j, G.Adj s (f j)) ∧ f i = w := by
  classical
  obtain ⟨f,hf,hA⟩ := representatives hk hS hs
  let r (j : Comp G S) := if j = i then w else f j
  have hSet (j : Comp G S) : r j ∈ ComponentSet G S j := by
    by_cases h : j = i
    · subst j
      simpa [r] using hw
    · simpa [r,h] using hf j
  have hinj : Function.Injective r := by
    intro x y hh
    by_cases h : x = y
    · exact h
    · exact (Set.disjoint_left.mp (componentSets_disjoint (G := G) h) (hSet x)
        (hh.symm ▸ hSet y)).elim
  refine ⟨⟨r,hinj⟩,hSet,?_,?_⟩
  · intro j
    change G.Adj s (r j)
    by_cases h : j = i <;> simp [r,h,he,hA]
  · change r i = w
    simp [r]

/-- With four deletion components and tree number at most five, the cut is
completely joined to its complement. -/
theorem four_components_full_cut (hk : ConnectivityAtLeast G 3) (ht : treeNumber G ≤ 5)
    {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 4) :
    ∀ s ∈ S, ∀ w ∉ S, G.Adj s w := by
  classical
  letI := compFintype G S
  intro s hs w hw
  by_cases he : G.Adj s w
  · exact he
  exfalso
  let i := (Deleted G S).connectedComponentMk ⟨w,hw⟩
  obtain ⟨x,hx,y,hy,hxA,hyN,hxy⟩ := near_far_edge hk hS hs
    (show w ∈ ComponentSet G S i from ⟨hw,rfl⟩) he
  obtain ⟨f,hf,hA,hfi⟩ := representatives_override hk hS hs hx hxA
  let z : Unit ↪ V := ⟨fun _ => y, fun a b _ => Subsingleton.elim a b⟩
  have hI (j k : Comp G S) : ¬ G.Adj (f j) (f k) := by
    by_cases h : j = k
    · subst k
      exact G.loopless _
    · exact componentSets_no_edges h (hf j) (hf k)
  have hZ (j : Comp G S) (u : Unit) : G.Adj (f j) (z u) ↔ j = i := by
    constructor
    · intro e
      by_cases h : j = i
      · exact h
      · exact (componentSets_no_edges h (hf j) hy e).elim
    · rintro rfl
      simpa only [hfi] using hxy
  have hB := extended_star_bound s f z (fun _ => i) hA hI
    (fun _ hh => by change y = s at hh; exact hy.1 (hh.symm ▸ hs))
    (fun j _ hh => by change y = f j at hh; exact hyN (hh.symm ▸ hA j))
    (fun _ => hyN) (fun _ _ => G.loopless _) hZ
  have hq' : Fintype.card (Comp G S) = 4 := hq
  simp only [Fintype.card_unit,hq'] at hB
  omega

/-- Each of four deletion components is a clique under the catalogue tree bound. -/
theorem four_components_cliques (hk : ConnectivityAtLeast G 3) (ht : treeNumber G ≤ 5)
    {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 4)
    (i : Comp G S) :
    ∀ ⦃a b⦄, a ∈ ComponentSet G S i → b ∈ ComponentSet G S i → a ≠ b → G.Adj a b := by
  classical
  letI := compFintype G S
  have hq' : Fintype.card (Comp G S) = 4 := hq
  intro a b ha hb hne
  by_cases he : G.Adj a b
  · exact he
  exfalso
  obtain ⟨s,hs⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hjoin := four_components_full_cut hk ht hS hq s hs
  obtain ⟨f,hf,hA,hfi⟩ := representatives_override hk hS hs ha (hjoin a ha.1)
  have neat (j : Comp G S) : f j ≠ b := by
    intro hh
    by_cases h : j = i
    · subst j
      exact hne (hfi.symm.trans hh)
    · exact Set.disjoint_left.mp (componentSets_disjoint h) (hf j) (hh.symm ▸ hb)
  have nAdj (j : Comp G S) : ¬ G.Adj (f j) b := by
    by_cases h : j = i
    · subst j
      simpa only [hfi] using he
    · exact componentSets_no_edges h (hf j) hb
  let g : Option (Comp G S) → V
    | none => b
    | some j => f j
  have inj : Function.Injective g := by
    intro x y hp
    rcases x with - | x <;> rcases y with - | y
    · rfl
    · exact (neat y hp.symm).elim
    · exact (neat x hp).elim
    · exact congrArg some (f.injective hp)
  let F : Option (Comp G S) ↪ V := ⟨g,inj⟩
  have hF (j : Option (Comp G S)) : G.Adj s (F j) := by
    cases j with
    | none => exact hjoin b hb.1
    | some j => exact hA j
  have hN (j k : Option (Comp G S)) : ¬ G.Adj (F j) (F k) := by
    rcases j with - | j <;> rcases k with - | k
    · exact G.loopless _
    · exact fun h => nAdj k h.symm
    · exact nAdj j
    · by_cases h : j = k
      · subst k
        exact G.loopless _
      · exact componentSets_no_edges h (hf j) (hf k)
  have hB := independent_neighbors_card_bound s F hF hN
  simp only [Fintype.card_option,hq'] at hB
  omega

/-- A three-cut with four deletion components suffices for the conclusion. -/
theorem traceable_of_four_components (hk : ConnectivityAtLeast G 3) (ht : treeNumber G ≤ 5)
    {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 4) :
    Traceable G := by
  classical
  letI := compFintype G S
  have hn : Fintype.card (Comp G S) = 4 := hq
  let E := (Fintype.equivFinOfCardEq hn).symm
  let s := (Finset.equivFinOfCardEq hS).symm
  let A (i : Fin 4) := ComponentSet G S (E i)
  let r (i : Fin 4) : PathOn G (A i) := PathOn.ofClique (by
    obtain ⟨a,ha⟩ := (E i).exists_rep
    exact ⟨a.val,a.property,ha⟩) (four_components_cliques hk ht hS hq (E i))
  have dRR (i j : Fin 4) (h : i ≠ j) : Disjoint (A i) (A j) :=
    componentSets_disjoint (E.injective.ne h)
  have dRS (i : Fin 4) (j : Fin 3) : Disjoint (A i) ({(s j).val} : Set V) :=
    Set.disjoint_singleton_right.mpr (fun he => he.1 (s j).property)
  have dSS (i j : Fin 3) (h : i ≠ j) : Disjoint ({(s i).val} : Set V) {(s j).val} := by
    have hne : (s i).val ≠ (s j).val := fun he => h (s.injective (Subtype.ext he))
    simp [hne]
  have hjoin := four_components_full_cut hk ht hS hq
  let p1 := (r 0).join (PathOn.singleton (s 0).val) ((dRS 0 0))
    (by simpa using (hjoin _ (s 0).property _ (r 0).last_mem.1).symm)
  let p2 := p1.join (r 1) (Set.disjoint_union_left.mpr ⟨(dRR 0 1 (by decide)),(dRS 1 0).symm⟩)
    (by simpa [p1] using hjoin _ (s 0).property _ (r 1).first_mem.1)
  let p3 := p2.join (PathOn.singleton (s 1).val) (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨(dRS 0 1),(dSS 0 1 (by decide))⟩,(dRS 1 1)⟩)
    (by simpa [p1,p2] using (hjoin _ (s 1).property _ (r 1).last_mem.1).symm)
  let p4 := p3.join (r 2) (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨(dRR 0 2 (by decide)),(dRS 2 0).symm⟩,(dRR 1 2 (by decide))⟩,(dRS 2 1).symm⟩)
    (by simpa [p1,p2,p3] using hjoin _ (s 1).property _ (r 2).first_mem.1)
  let p5 := p4.join (PathOn.singleton (s 2).val) (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨(dRS 0 2),(dSS 0 2 (by decide))⟩,(dRS 1 2)⟩,(dSS 1 2 (by decide))⟩,(dRS 2 2)⟩)
    (by simpa [p1,p2,p3,p4] using (hjoin _ (s 2).property _ (r 2).last_mem.1).symm)
  let p6 := p5.join (r 3) (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨(dRR 0 3 (by decide)),(dRS 3 0).symm⟩,(dRR 1 3 (by decide))⟩,(dRS 3 1).symm⟩,(dRR 2 3 (by decide))⟩,(dRS 3 2).symm⟩)
    (by simpa [p1,p2,p3,p4,p5] using hjoin _ (s 2).property _ (r 3).first_mem.1)

  have hU : ((((((A 0 ∪ {(s 0).val}) ∪ A 1) ∪ {(s 1).val}) ∪ A 2) ∪ {(s 2).val}) ∪ A 3)
      = (Set.univ : Set V) := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨j,hj⟩ := s.surjective ⟨x,hx⟩
      have he : (s j).val = x := congrArg Subtype.val hj
      rw [← he]
      fin_cases j <;> simp
    · obtain ⟨j,hj⟩ := E.surjective ((Deleted G S).connectedComponentMk ⟨x,hx⟩)
      have hm : x ∈ A j := ⟨hx,hj.symm⟩
      fin_cases j
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))
      · exact Or.inl (Or.inl (Or.inr hm))
      · exact Or.inr hm
  exact (p6.cast hU).traceable

/-- The earlier tree bound suffices at every connectivity of at least two. -/
theorem traceable_of_treeNumber_le_four (hc : G.Connected)
    (hk : ConnectivityAtLeast G 2) (ht : treeNumber G ≤ 4) : Traceable G := by
  classical
  by_cases hC : ∃ Q, IsClaw G Q
  · by_cases hd : EveryClawDominates G
    · obtain ⟨Q,hQ⟩ := hC
      exact dominating_claw_traceable hc hk ht hd Q hQ
    · unfold EveryClawDominates at hd
      push_neg at hd
      obtain ⟨Q,hQ,y,ho,hn⟩ := hd
      exact nondominating_claw_traceable ht hc hk hQ
        ⟨y,ho,fun i => iff_of_false (hn i) (by simp)⟩
  · push_neg at hC
    exact ClawFreeCase.claw_free_traceable hc hk ht hC

private theorem complete_when_connectivity_high (hc : G.Connected) {k : ℕ}
    (hk : ConnectivityAtLeast G k) (hn : Fintype.card V ≤ k+1) : Traceable G := by
  classical
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have hE : ∀ ⦃a b : V⦄, a ≠ b → G.Adj a b := by
    intro a b hab
    by_cases he : G.Adj a b
    · exact he
    exfalso
    let R := G.neighborFinset a
    have ha : a ∉ R := by simp [R]
    have hb : b ∉ R := by simpa [R] using he
    have hba : a ∉ insert b R := by simp [hab,ha]
    have hl := Finset.card_le_univ (insert a (insert b R))
    rw [Finset.card_insert_of_not_mem hba,Finset.card_insert_of_not_mem hb] at hl
    have hMin : k ≤ R.card := min_degree_of_connectivityAtLeast hk a
    omega
  exact (PathOn.ofClique (G := G) (A := Set.univ)
    (by obtain ⟨v⟩ := hc.nonempty; exact ⟨v,Set.mem_univ _⟩)
    (fun ⦃a b⦄ _ _ h => hE h)).traceable

private theorem three_cut_exists [Nonempty V] (hk : vertexConnectivity G = 3)
    (ho : 4 < Fintype.card V) :
    ∃ S : Finset V, S.card = 3 ∧ ¬ (Deleted G S).Connected := by
  classical
  have h3 : ConnectivityAtLeast G 3 := hk ▸ connectivityAtLeast_vertexConnectivity G
  have h4 : ¬ ConnectivityAtLeast G 4 := by
    intro h
    have hle : 4 ≤ vertexConnectivity G := by
      unfold vertexConnectivity
      exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1,h⟩)
    omega
  have hC : ∃ S : Finset V, S.card < 4 ∧ ¬(G.induce ((↑S : Set V)ᶜ)).Connected := by
    by_contra! h
    exact h4 ⟨ho,h⟩
  obtain ⟨S,hs,hn⟩ := hC
  have hS : S.card = 3 := by
    by_contra h
    exact hn (h3.2 S (by omega))
  exact ⟨S,hS,hn⟩

/-- A counterexample at connectivity three must have tree number five and each
minimum vertex cut must leave two or three components. -/
theorem connectivity_three_remaining [Nonempty V] (hc : G.Connected) (hk : vertexConnectivity G = 3)
    (ht : treeNumber G ≤ 5) (hnt : ¬ Traceable G) :
    treeNumber G = 5 ∧
    (∃ S : Finset V, S.card = 3 ∧ ¬ (Deleted G S).Connected) ∧
    ∀ S : Finset V, S.card = 3 → ¬ (Deleted G S).Connected →
      letI := compFintype G S
      Fintype.card (Comp G S) = 2 ∨ Fintype.card (Comp G S) = 3 := by
  classical
  have h3 : ConnectivityAtLeast G 3 := hk ▸ connectivityAtLeast_vertexConnectivity G
  have h2 : ConnectivityAtLeast G 2 := ⟨by have h := h3.1; omega,
    fun S hs => h3.2 S (by omega)⟩
  have ht4 : ¬ treeNumber G ≤ 4 := fun h => hnt (traceable_of_treeNumber_le_four hc h2 h)
  have ho : 4 < Fintype.card V := by
    by_contra! hh
    exact hnt (complete_when_connectivity_high hc h3 hh)
  refine ⟨by omega,three_cut_exists hk ho,?_⟩
  intro S hS hD
  letI := compFintype G S
  have upper : Fintype.card (Comp G S) + 1 ≤ treeNumber G := component_card_tree_bound h3 hS
  have h4 : Fintype.card (Comp G S) ≠ 4 := fun h =>
    hnt (traceable_of_four_components h3 ht hS h)
  have lower : 2 ≤ Fintype.card (Comp G S) := by
    by_contra! h
    have hsub : Subsingleton (Comp G S) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨x,_,hx⟩ := Finset.exists_mem_not_mem_of_card_lt_card
      (show S.card < (Finset.univ : Finset V).card by rw [hS,Finset.card_univ]; omega)
    exact hD (@SimpleGraph.Connected.mk (Rem S) (Deleted G S)
      (fun a b => SimpleGraph.ConnectedComponent.exact (hsub.elim _ _)) ⟨x,hx⟩)
  omega

/-- A component meeting the cut vertex at every vertex, and inducing a clique. -/
def PerfectComponent (G : SimpleGraph V) (S : Finset V) (s : V) (i : Comp G S) : Prop :=
  (∀ x ∈ ComponentSet G S i, G.Adj s x) ∧
    (∀ ⦃x y⦄, x ∈ ComponentSet G S i → y ∈ ComponentSet G S i → x ≠ y → G.Adj x y)

private theorem branch_of_imperfect (hk : ConnectivityAtLeast G 3) {S : Finset V}
    (hS : S.card = 3) {s : V} (hs : s ∈ S) {i : Comp G S}
    (hi : ¬ PerfectComponent G S s i) :
    ∃ x ∈ ComponentSet G S i, ∃ y ∈ ComponentSet G S i,
      x ≠ y ∧ G.Adj s x ∧ (G.Adj x y ↔ ¬ G.Adj s y) := by
  classical
  by_cases ha : ∀ x ∈ ComponentSet G S i, G.Adj s x
  · have nc : ¬ (∀ x y, x ∈ ComponentSet G S i → y ∈ ComponentSet G S i →
        x ≠ y → G.Adj x y) := fun h => hi ⟨ha,fun ⦃x y⦄ => h x y⟩
    push_neg at nc
    obtain ⟨x,y,hx,hy,hn,he⟩ := nc
    exact ⟨x,hx,y,hy,hn,ha x hx,⟨fun h => (he h).elim,fun h => (h (ha y hy)).elim⟩⟩
  · push_neg at ha
    obtain ⟨w,hw,he⟩ := ha
    obtain ⟨x,hx,y,hy,hsx,hn,hxy⟩ := near_far_edge hk hS hs hw he
    exact ⟨x,hx,y,hy,hxy.ne,hsx,⟨fun _ => hn,fun _ => hxy⟩⟩

/-- An imperfect component costs an additional vertex in an induced tree centered
at the specified cut vertex. -/
theorem imperfect_component_tree_budget [Fintype J] (hk : ConnectivityAtLeast G 3)
    {S : Finset V} (hS : S.card = 3) {s : V} (hs : s ∈ S)
    (indices : J ↪ Comp G S) (hi : ∀ j, ¬ PerfectComponent G S s (indices j)) :
    letI := compFintype G S
    Fintype.card (Comp G S) + Fintype.card J + 1 ≤ treeNumber G := by
  classical
  letI := compFintype G S
  choose a ha b hb hab haAdj hz using fun j => branch_of_imperfect hk hS hs (hi j)
  obtain ⟨base,hbase,hA⟩ := representatives hk hS hs
  let f (i : Comp G S) := if he : ∃ j, indices j = i then a (Classical.choose he) else base i
  have hf (i : Comp G S) : f i ∈ ComponentSet G S i := by
    by_cases h : ∃ j, indices j = i
    · simp only [f,dif_pos h]
      exact Eq.mp (congrArg
        (fun j => a (Classical.choose h) ∈ ComponentSet G S j) (Classical.choose_spec h))
        (ha (Classical.choose h))
    · simpa [f,h] using hbase i
  have hF (i : Comp G S) : G.Adj s (f i) := by
    by_cases h : ∃ j, indices j = i
    · simp only [f,dif_pos h]
      exact haAdj _
    · simpa [f,h] using hA i
  have heq (j : J) : f (indices j) = a j := by
    let h : ∃ k, indices k = indices j := ⟨j,rfl⟩
    simp only [f,dif_pos h]
    exact congrArg a (indices.injective (Classical.choose_spec h))
  have injf : Function.Injective f := by
    intro i j eq
    by_cases h : i = j
    · exact h
    · exact (Set.disjoint_left.mp (componentSets_disjoint h) (hf i) (eq.symm ▸ hf j)).elim
  have injb : Function.Injective b := by
    intro i j eq
    by_cases h : i = j
    · exact h
    · exact (Set.disjoint_left.mp (componentSets_disjoint (indices.injective.ne h))
        (hb i) (eq.symm ▸ hb j)).elim
  have hI (i j : Comp G S) : ¬ G.Adj (f i) (f j) := by
    by_cases h : i = j
    · subst j
      exact G.loopless _
    · exact componentSets_no_edges h (hf i) (hf j)
  have hB (i j : J) : ¬ G.Adj (b i) (b j) := by
    by_cases h : i = j
    · subst j
      exact G.loopless _
    · exact componentSets_no_edges (indices.injective.ne h) (hb i) (hb j)
  have hne (i : Comp G S) (j : J) : b j ≠ f i := by
    intro he
    by_cases h : i = indices j
    · subst i
      exact hab j ((he.trans (heq j)).symm)
    · exact Set.disjoint_left.mp (componentSets_disjoint h) (hf i) (he ▸ hb j)
  have hit (i : Comp G S) (j : J) :
      G.Adj (f i) (b j) ↔ i = indices j ∧ ¬ G.Adj s (b j) := by
    by_cases h : i = indices j
    · subst i
      simpa only [heq,eq_self_iff_true,true_and] using hz j
    · exact ⟨fun he => (componentSets_no_edges h (hf i) (hb j) he).elim,
        fun he => (h he.1).elim⟩
  exact rooted_star_bound s ⟨f,injf⟩ ⟨b,injb⟩ indices (fun j => G.Adj s (b j))
    hF hI (fun j he => by change b j = s at he; exact (hb j).1 (he.symm ▸ hs)) hne (fun _ => Iff.rfl) hB hit

/-- If a three-cut leaves three components, each cut vertex has at most one
component that is not a clique completely joined to that vertex. -/
theorem three_components_at_most_one_imperfect (hk : ConnectivityAtLeast G 3) (ht : treeNumber G ≤ 5)
    {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 3)
    {s : V} (hs : s ∈ S) {i j : Comp G S} (hne : i ≠ j) :
    PerfectComponent G S s i ∨ PerfectComponent G S s j := by
  classical
  letI := compFintype G S
  by_cases hi : PerfectComponent G S s i
  · exact Or.inl hi
  by_cases hj : PerfectComponent G S s j
  · exact Or.inr hj
  exfalso
  let f : Fin 2 → Comp G S := ![i,j]
  have inj : Function.Injective f := List.nodup_ofFn.mp (show [i,j].Nodup by simp [hne])
  let E : Fin 2 ↪ Comp G S := ⟨f,inj⟩
  have hI : ∀ k, ¬ PerfectComponent G S s (E k) := by
    intro k
    fin_cases k <;> assumption
  have hB := imperfect_component_tree_budget hk hS hs E hI
  have hq' : Fintype.card (Comp G S) = 3 := hq
  simp only [Fintype.card_fin,hq'] at hB
  omega



private theorem clique_from_start (A : Set V) {x : V} (hx : x ∈ A)
    (hc : ∀ ⦃a b⦄, a ∈ A → b ∈ A → a ≠ b → G.Adj a b) :
    ∃ p : PathOn G A, p.first = x := by
  classical
  let C := A \ ({x} : Set V)
  by_cases hC : C.Nonempty
  · let q : PathOn G C := PathOn.ofClique hC (fun ⦃a b⦄ ha hb h => hc ha.1 hb.1 h)
    have hd : Disjoint ({x} : Set V) C :=
      Set.disjoint_singleton_left.mpr (fun h => h.2 rfl)
    let p := (PathOn.singleton x).join q hd (hc hx q.first_mem.1 (fun e => q.first_mem.2 e.symm))
    have hSet : {x} ∪ C = A := by
      ext y
      by_cases h : y = x
      · subst y
        simp [hx]
      · simp [C,h]
    exact ⟨p.cast hSet,by simp [p]⟩
  · have hSet : ({x} : Set V) = A := by
      ext y
      constructor
      · intro h
        have he : y = x := h
        exact he.symm ▸ hx
      · intro hy
        by_cases he : y = x
        · exact he
        · exact (hC ⟨y,hy,he⟩).elim
    exact ⟨(PathOn.singleton x).cast hSet,rfl⟩

private def GoodRow (m : Fin 8) : Prop :=
  ∀ i j : Fin 3, i ≠ j → m.val.testBit i.val = true ∨ m.val.testBit j.val = true

private instance (m : Fin 8) : Decidable (GoodRow m) := by unfold GoodRow; infer_instance

private def RowTable (m₀ m₁ m₂ : Fin 8) (i j : Fin 3) : Bool :=
  ((![m₀,m₁,m₂] : Fin 3 → Fin 8) i).val.testBit j.val

private theorem route_for_good_rows :
    ∀ a b c : Fin 8, GoodRow a → GoodRow b → GoodRow c →
      ∃ i j k p q r : Fin 3,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        RowTable a b c i p = true ∧ RowTable a b c j p = true ∧
        RowTable a b c j q = true ∧ RowTable a b c k q = true := by
  intro a
  fin_cases a <;> decide

private theorem realize_three_bits :
    ∀ f : Fin 3 → Bool, ∃ m : Fin 8, ∀ i : Fin 3, m.val.testBit i.val = f i := by decide

private theorem all_three_labels {i j k : Fin 3} (hi : i ≠ j) (hj : i ≠ k) (hk : j ≠ k) :
    ∀ v : Fin 3, v = i ∨ v = j ∨ v = k := by
  exact (by decide : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∀ v : Fin 3, v = a ∨ v = b ∨ v = c) i j k hi hj hk

/-- A three-cut whose three deletion components are cliques yields a Hamiltonian path. -/
theorem traceable_of_three_clique_components (hk : ConnectivityAtLeast G 3)
    (ht : treeNumber G ≤ 5) {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 3)
    (hCl : ∀ i : Comp G S, ∀ ⦃a b⦄,
      a ∈ ComponentSet G S i → b ∈ ComponentSet G S i → a ≠ b → G.Adj a b) :
    Traceable G := by
  classical
  letI := compFintype G S
  have hq' : Fintype.card (Comp G S) = 3 := hq
  let C := (Fintype.equivFinOfCardEq hq').symm
  let s := (Finset.equivFinOfCardEq hS).symm
  let A (i : Fin 3) := ComponentSet G S (C i)
  let full (i j : Fin 3) := ∀ v ∈ A j, G.Adj (s i).val v
  let mat (i j : Fin 3) := decide (full i j)
  have good (i j k : Fin 3) (hne : j ≠ k) : full i j ∨ full i k :=
    (three_components_at_most_one_imperfect hk ht hS hq (s i).property
      (C.injective.ne hne)).imp And.left And.left
  obtain ⟨m₀,hm₀⟩ := realize_three_bits (mat 0)
  obtain ⟨m₁,hm₁⟩ := realize_three_bits (mat 1)
  obtain ⟨m₂,hm₂⟩ := realize_three_bits (mat 2)
  have hRow (i j : Fin 3) : RowTable m₀ m₁ m₂ i j = mat i j := by
    fin_cases i
    · exact hm₀ j
    · exact hm₁ j
    · exact hm₂ j
  have hGood (i : Fin 3) : GoodRow ((![m₀,m₁,m₂] : Fin 3 → Fin 8) i) := by
    intro j k h
    change RowTable m₀ m₁ m₂ i j = true ∨ RowTable m₀ m₁ m₂ i k = true
    simpa [hRow,mat] using good i j k h
  obtain ⟨i,j,k,a,b,c,hij,hik,hjk,hab,hac,hbc,hIa,hJa,hJb,hKb⟩ :=
    route_for_good_rows m₀ m₁ m₂ (hGood 0) (hGood 1) (hGood 2)
  have fa : full i a := by have e := hIa; simpa [hRow,mat] using e
  have ga : full j a := by have e := hJa; simpa [hRow,mat] using e
  have gb : full j b := by have e := hJb; simpa [hRow,mat] using e
  have fb : full k b := by have e := hKb; simpa [hRow,mat] using e
  let path (n : Fin 3) : PathOn G (A n) := PathOn.ofClique (by
    obtain ⟨x,hx⟩ := (C n).exists_rep
    exact ⟨x.val,x.property,hx⟩) (hCl (C n))
  obtain ⟨x,hx,he⟩ := cut_touches_components hk hS (s k).property (C c)
  obtain ⟨endPath,hf⟩ := clique_from_start (A c) ⟨x.property,hx⟩ (hCl (C c))
  let cut (n : Fin 3) : Set V := {(s n).val}
  let pts (n : Fin 3) : PathOn G (cut n) := PathOn.singleton (s n).val
  have dAA (i j : Fin 3) (h : i ≠ j) : Disjoint (A i) (A j) :=
    componentSets_disjoint (C.injective.ne h)
  have dAC (i j : Fin 3) : Disjoint (A i) (cut j) :=
    Set.disjoint_singleton_right.mpr (fun e => e.1 (s j).property)
  have dCC (i j : Fin 3) (h : i ≠ j) : Disjoint (cut i) (cut j) := by
    have hne : (s i).val ≠ (s j).val := fun e => h (s.injective (Subtype.ext e))
    simp [cut,hne]
  let p1 := (pts i).join (path a) (dAC a i).symm (fa _ (path a).first_mem)
  let p2 := p1.join (pts j) (Set.disjoint_union_left.mpr ⟨dCC i j hij,dAC a j⟩)
    (by simpa [p1,pts] using (ga _ (path a).last_mem).symm)
  let p3 := p2.join (path b) (Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨(dAC b i).symm,dAA a b hab⟩,(dAC b j).symm⟩)
    (by simpa [p2,pts] using gb _ (path b).first_mem)
  let p4 := p3.join (pts k) (Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨dCC i k hik,dAC a k⟩,dCC j k hjk⟩,dAC b k⟩)
    (by simpa [p3,pts] using (fb _ (path b).last_mem).symm)
  let p5 := p4.join endPath (Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨(dAC c i).symm,dAA a c hac⟩,(dAC c j).symm⟩,
        dAA b c hbc⟩,(dAC c k).symm⟩) (by simpa [p4,pts,hf] using he)
  have hSet : (((((cut i ∪ A a) ∪ cut j) ∪ A b) ∪ cut k) ∪ A c) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    by_cases hh : v ∈ S
    · obtain ⟨z,hz⟩ := s.surjective ⟨v,hh⟩
      have hEq : v = (s z).val := (congrArg Subtype.val hz).symm
      rcases all_three_labels hij hik hjk z with h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h ▸ hEq)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (h ▸ hEq))))
      · exact Or.inl (Or.inr (h ▸ hEq))
    · obtain ⟨z,hz⟩ := C.surjective ((Deleted G S).connectedComponentMk ⟨v,hh⟩)
      have hv : v ∈ A z := ⟨hh,hz.symm⟩
      rcases all_three_labels hab hac hbc z with h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h ▸ hv)))))
      · exact Or.inl (Or.inl (Or.inr (h ▸ hv)))
      · exact Or.inr (h ▸ hv)
  exact (p5.cast hSet).traceable

/-- In the three-component branch, any hypothetical counterexample must have a
nonclique component. The other two components are cliques joined to the cut. -/
theorem three_component_counterexample_structure (hk : ConnectivityAtLeast G 3)
    (ht : treeNumber G ≤ 5) {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 3)
    (hn : ¬ Traceable G) :
    ∃ i : Comp G S,
      (∃ a ∈ ComponentSet G S i, ∃ b ∈ ComponentSet G S i, a ≠ b ∧ ¬ G.Adj a b) ∧
      ∀ j : Comp G S, j ≠ i → ∀ s ∈ S, PerfectComponent G S s j := by
  classical
  have h : ¬ (∀ i : Comp G S, ∀ a b : V,
      a ∈ ComponentSet G S i → b ∈ ComponentSet G S i → a ≠ b → G.Adj a b) :=
    fun hh => hn (traceable_of_three_clique_components hk ht hS hq (fun i ⦃a b⦄ => hh i a b))
  push_neg at h
  obtain ⟨i,a,b,ha,hb,hab,he⟩ := h
  refine ⟨i,⟨a,ha,b,hb,hab,he⟩,?_⟩
  intro j hji s hs
  rcases three_components_at_most_one_imperfect hk ht hS hq hs hji.symm with hi | hj
  · exact (he (hi.2 ha hb hab)).elim
  · exact hj


private theorem clique_from_two_ends (A : Set V) {a b : V} (ha : a ∈ A) (hb : b ∈ A) (hn : a ≠ b)
    (hc : ∀ ⦃x y⦄, x ∈ A → y ∈ A → x ≠ y → G.Adj x y) :
    ∃ p : PathOn G A, p.first = a ∧ p.last = b := by
  classical
  let X := A \ ({a,b} : Set V)
  have omit_ends (x : V) (hx : x ∈ X) : x ≠ a ∧ x ≠ b := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using hx.2
  obtain ⟨p,hf,hl⟩ := PathOn.clique_between X hn (fun h => (omit_ends a h).1 rfl)
    (fun h => (omit_ends b h).2 rfl) (fun _ => hc ha hb hn)
    (fun ⦃a b⦄ ha hb h => hc ha.1 hb.1 h)
    (fun x hx => ⟨hc ha hx.1 (omit_ends x hx).1.symm,hc hx.1 hb (omit_ends x hx).2⟩)
  have hSet : {a,b} ∪ X = A := by
    ext x
    by_cases h1 : x = a
    · subst x
      simp [ha]
    by_cases h2 : x = b
    · subst x
      simp [hb]
    simp [X,h1,h2]
  exact ⟨p.cast hSet,hf,hl⟩

private def CanPass (G : SimpleGraph V) (A : Set V) (s t : V) : Prop :=
  ∃ p : PathOn G A, G.Adj s p.first ∧ G.Adj t p.last

omit [Fintype V] in
private theorem CanPass.reverse {A : Set V} {s t : V} (h : CanPass G A s t) :
    CanPass G A t s := by
  obtain ⟨p,hp,hq⟩ := h
  exact ⟨p.reverse,by simpa using hq,by simpa using hp⟩

private theorem crossing_avoiding (hk : ConnectivityAtLeast G 3)
    (A : Set V) {a b z : V} (ha : a ∈ A) (hb : b ∉ A) (hza : a ≠ z) (hzb : b ≠ z) :
    ∃ x ∈ A, ∃ y ∉ A, x ≠ z ∧ y ≠ z ∧ G.Adj x y := by
  classical
  let X := ((↑({z} : Finset V) : Set V)ᶜ)
  have h := hk.2 {z} (by simp)
  have ha' : a ∈ X := by simpa [X] using hza
  have hb' : b ∈ X := by simpa [X] using hzb
  obtain ⟨x,hx,y,hy,he⟩ := graph_cut h {v : ↑X | v.val ∈ A}
    (show (⟨a,ha'⟩ : X) ∈ {v : ↑X | v.val ∈ A} from ha)
    (show (⟨b,hb'⟩ : X) ∉ {v : ↑X | v.val ∈ A} from hb)
  exact ⟨x.val,hx,y.val,hy,by simpa [X] using x.property,
    by simpa [X] using y.property,he⟩

private theorem clique_component_good_pairs (hk : ConnectivityAtLeast G 3)
    {S : Finset V} (hS : S.card = 3) {i j : Comp G S} (hij : i ≠ j)
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S)
    (hSall : ∀ v ∈ S, v = a ∨ v = b ∨ v = c)
    (hClique : ∀ ⦃x y⦄, x ∈ ComponentSet G S i → y ∈ ComponentSet G S i →
      x ≠ y → G.Adj x y) :
    CanPass G (ComponentSet G S i) a b ∨ CanPass G (ComponentSet G S i) b c := by
  classical
  let A := ComponentSet G S i
  by_cases hFirst : CanPass G A a b
  · exact Or.inl hFirst
  by_cases hSecond : CanPass G A b c
  · exact Or.inr hSecond
  exfalso
  obtain ⟨z,hz,hbz⟩ := cut_touches_components hk hS hb i
  obtain ⟨u,hu,hau⟩ := cut_touches_components hk hS ha i
  have hz' : z.val ∈ A := ⟨z.property,hz⟩
  have hu' : u.val ∈ A := ⟨u.property,hu⟩
  have bad_pair {s t : V} (hh : ¬CanPass G A s t) {x y : V}
      (hx : x ∈ A) (hy : y ∈ A) (hxs : G.Adj s x) (hyt : G.Adj t y) : x = y := by
    by_contra he
    obtain ⟨p,hf,hl⟩ := clique_from_two_ends A hx hy he hClique
    exact hh ⟨p,hf.symm ▸ hxs,hl.symm ▸ hyt⟩
  have huz : u.val = z.val := bad_pair hFirst hu' hz' hau hbz
  have haz : G.Adj a z.val := huz ▸ hau
  have only_z (x : V) (hx : x ∈ A) (s : V) (hs : s ∈ S) (hAdj : G.Adj s x) : x = z.val := by
    rcases hSall s hs with eq | eq | eq
    · exact bad_pair hFirst hx hz' (eq ▸ hAdj) hbz
    · exact (bad_pair hFirst hz' hx haz (eq ▸ hAdj)).symm
    · exact (bad_pair hSecond hz' hx hbz (eq ▸ hAdj)).symm
  by_cases hs : ∃ w ∈ A, w ≠ z.val
  · obtain ⟨w,hw,hwz⟩ := hs
    obtain ⟨q,hq⟩ := j.exists_rep
    have hq' : q.val ∈ ComponentSet G S j := ⟨q.property,hq⟩
    have hqn : q.val ∉ A := fun he =>
      Set.disjoint_left.mp (componentSets_disjoint hij) he hq'
    have hqz : q.val ≠ z.val := fun he => hqn (he.symm ▸ hz')
    obtain ⟨x,hx,y,hy,hxz,_,he⟩ := crossing_avoiding hk A hw hqn hwz hqz
    have hyS : y ∈ S := by
      by_contra hy'
      let r := (Deleted G S).connectedComponentMk ⟨y,hy'⟩
      have hyr : y ∈ ComponentSet G S r := ⟨hy',rfl⟩
      have hei : i ≠ r := fun eq => hy (show y ∈ ComponentSet G S i from eq.symm ▸ hyr)
      exact componentSets_no_edges hei hx hyr he
    exact hxz (only_z x hx y hyS he.symm)
  · have hSet : ({z.val} : Set V) = A := by
      ext x
      constructor
      · intro hx
        have e : x = z.val := hx
        exact e.symm ▸ hz'
      · intro hx
        by_cases he : x = z.val
        · exact he
        · exact (hs ⟨x,hx,he⟩).elim
    exact hFirst ⟨(PathOn.singleton z.val).cast hSet,haz,hbz⟩

/-- A three-cut with two clique components also yields a Hamiltonian path. -/
theorem traceable_of_two_clique_components (hk : ConnectivityAtLeast G 3)
    {S : Finset V} (hS : S.card = 3)
    (hq : letI := compFintype G S; Fintype.card (Comp G S) = 2)
    (hCl : ∀ i : Comp G S, ∀ ⦃a b⦄,
      a ∈ ComponentSet G S i → b ∈ ComponentSet G S i → a ≠ b → G.Adj a b) :
    Traceable G := by
  classical
  letI := compFintype G S
  have hq' : Fintype.card (Comp G S) = 2 := hq
  let E := (Fintype.equivFinOfCardEq hq').symm
  let A := ComponentSet G S (E 0)
  let B := ComponentSet G S (E 1)
  let s := (Finset.equivFinOfCardEq hS).symm
  let C (i : Fin 3) : Set V := {(s i).val}
  have allS (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ∀ v ∈ S, v = (s i).val ∨ v = (s j).val ∨ v = (s k).val := by
    intro v hv
    obtain ⟨a,ha⟩ := s.surjective ⟨v,hv⟩
    have eq : v = (s a).val := (congrArg Subtype.val ha).symm
    rcases all_three_labels hij hik hjk a with h | h | h
    · exact Or.inl (h ▸ eq)
    · exact Or.inr (Or.inl (h ▸ eq))
    · exact Or.inr (Or.inr (h ▸ eq))
  have dAB : E 0 ≠ E 1 := E.injective.ne (by decide)
  have pA : CanPass G A (s 0).val (s 1).val ∨ CanPass G A (s 1).val (s 2).val :=
    clique_component_good_pairs hk hS dAB (s 0).property (s 1).property
      (allS 0 1 2 (by decide) (by decide) (by decide)) (hCl (E 0))
  have order : ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      CanPass G A (s i).val (s j).val ∧ CanPass G B (s j).val (s k).val := by
    rcases pA with pa | pa
    · have pb := clique_component_good_pairs hk hS dAB.symm
        (s 1).property (s 2).property
        (allS 1 2 0 (by decide) (by decide) (by decide)) (hCl (E 1))
      rcases pb with pb | pb
      · exact ⟨0,1,2,by decide,by decide,by decide,pa,pb⟩
      · exact ⟨1,0,2,by decide,by decide,by decide,pa.reverse,pb.reverse⟩
    · have pb := clique_component_good_pairs hk hS dAB.symm
        (s 2).property (s 0).property
        (allS 2 0 1 (by decide) (by decide) (by decide)) (hCl (E 1))
      rcases pb with pb | pb
      · exact ⟨1,2,0,by decide,by decide,by decide,pa,pb⟩
      · exact ⟨2,1,0,by decide,by decide,by decide,pa.reverse,pb.reverse⟩
  obtain ⟨i,j,k,hij,hik,hjk,⟨p,hp1,hp2⟩,⟨q,hq1,hq2⟩⟩ := order
  let pts (i : Fin 3) : PathOn G (C i) := PathOn.singleton (s i).val
  have dAC (i : Fin 3) : Disjoint A (C i) :=
    Set.disjoint_singleton_right.mpr (fun e => e.1 (s i).property)
  have dBC (i : Fin 3) : Disjoint B (C i) :=
    Set.disjoint_singleton_right.mpr (fun e => e.1 (s i).property)
  have dCC (i j : Fin 3) (h : i ≠ j) : Disjoint (C i) (C j) := by
    have hne : (s i).val ≠ (s j).val := fun e => h (s.injective (Subtype.ext e))
    simp [C,hne]
  let p₁ := (pts i).join p (dAC i).symm hp1
  let p₂ := p₁.join (pts j) (Set.disjoint_union_left.mpr ⟨dCC i j hij,dAC j⟩)
    (by simpa [p₁,pts] using hp2.symm)
  let p₃ := p₂.join q (Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨(dBC i).symm,componentSets_disjoint dAB⟩,(dBC j).symm⟩)
    (by simpa [p₂,pts] using hq1)
  let p₄ := p₃.join (pts k) (Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨dCC i k hik,dAC k⟩,dCC j k hjk⟩,dBC k⟩)
    (by simpa [p₃,pts] using hq2.symm)
  have hSet : ((((C i ∪ A) ∪ C j) ∪ B) ∪ C k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    by_cases h : v ∈ S
    · rcases allS i j k hij hik hjk v h with ha | hb | hc
      · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
      · exact Or.inl (Or.inl (Or.inr hb))
      · exact Or.inr hc
    · obtain ⟨a,ha⟩ := E.surjective ((Deleted G S).connectedComponentMk ⟨v,h⟩)
      have hc : v ∈ ComponentSet G S (E a) := ⟨h,ha.symm⟩
      fin_cases a
      · exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
      · exact Or.inl (Or.inr hc)
  exact (p₄.cast hSet).traceable


/-- Every minimum cut of a possible connectivity-three counterexample leaves
two or three components, at least one of which is nonclique. -/
theorem connectivity_three_nonclique_remaining [Nonempty V] (hc : G.Connected)
    (hk : vertexConnectivity G = 3) (ht : treeNumber G ≤ 5) (hn : ¬ Traceable G)
    {S : Finset V} (hS : S.card = 3) (hD : ¬ (Deleted G S).Connected) :
    letI := compFintype G S
    (Fintype.card (Comp G S) = 2 ∨ Fintype.card (Comp G S) = 3) ∧
    ∃ i : Comp G S, ∃ a ∈ ComponentSet G S i, ∃ b ∈ ComponentSet G S i,
      a ≠ b ∧ ¬ G.Adj a b := by
  classical
  letI := compFintype G S
  have h3 : ConnectivityAtLeast G 3 := hk ▸ connectivityAtLeast_vertexConnectivity G
  have hq := (connectivity_three_remaining hc hk ht hn).2.2 S hS hD
  refine ⟨hq,?_⟩
  have h : ¬ (∀ i : Comp G S, ∀ a b : V,
      a ∈ ComponentSet G S i → b ∈ ComponentSet G S i → a ≠ b → G.Adj a b) := by
    intro he
    have hC (i : Comp G S) : ∀ ⦃a b⦄, a ∈ ComponentSet G S i → b ∈ ComponentSet G S i →
        a ≠ b → G.Adj a b := fun ⦃a b⦄ => he i a b
    rcases hq with h2 | h3'
    · exact hn (traceable_of_two_clique_components h3 hS h2 hC)
    · exact hn (traceable_of_three_clique_components h3 ht hS h3' hC)
  push_neg at h
  obtain ⟨i,a,b,ha,hb,hab,hn⟩ := h
  exact ⟨i,a,ha,b,hb,hab,hn⟩

#print axioms connectivity_three_nonclique_remaining
#print axioms traceable_of_two_clique_components
#print axioms three_component_counterexample_structure
#print axioms traceable_of_three_clique_components
#print axioms component_card_tree_bound
#print axioms traceable_of_four_components
#print axioms connectivity_three_remaining
#print axioms imperfect_component_tree_budget
#print axioms three_components_at_most_one_imperfect
end ThreeCut
end LowConnectivity
end Graffiti199K2
