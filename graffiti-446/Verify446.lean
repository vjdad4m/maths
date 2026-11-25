import Std
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti446
universe u

variable {V : Type u} [DecidableEq V]

structure Graph (V : Type u) where
  verts : List V
  nodup : verts.Nodup
  complete : ∀ v, v ∈ verts
  edge : V → V → Bool
  symm : ∀ v w, edge v w = true → edge w v = true
  loopless : ∀ v, edge v v = false

def Adj (G : Graph V) (v w : V) : Prop := G.edge v w = true

inductive Walk (G : Graph V) : V → V → Prop
  | nil {v} : Walk G v v
  | cons {u v w} : Adj G u v → Walk G v w → Walk G u w

def Connected (G : Graph V) : Prop := ∀ v w, Walk G v w

def cardinal (G : Graph V) (P : V → Bool) : Nat := (G.verts.filter P).length
def nbrs (G : Graph V) (P : V → Bool) (v : V) : List V :=
  G.verts.filter (fun w => G.edge v w && P w)
def degree (G : Graph V) (v : V) : Nat := (nbrs G (fun _ => true) v).length
def minimumDegreeSet (G : Graph V) (v : V) : Bool :=
  G.verts.all (fun w => decide (degree G v ≤ degree G w))
def leaf (G : Graph V) (v : V) : Bool := decide (degree G v = 1)
def leafNeighbors (G : Graph V) (v : V) : List V := nbrs G (leaf G) v
def support (G : Graph V) (v : V) : Bool := decide (0 < (leafNeighbors G v).length)
def privateNeighbor (G : Graph V) (A : V → Bool) (v : V) : Bool :=
  decide ((nbrs G A v).length = 1)
def TwoIndependent (G : Graph V) (I : V → Bool) : Prop :=
  ∀ v, I v = true → (nbrs G I v).length ≤ 1

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

theorem mem_nbrs {G : Graph V} {P : V → Bool} {v w} :
    w ∈ nbrs G P v ↔ Adj G v w ∧ P w = true := by
  simp [nbrs, Adj, G.complete]

theorem leaf_degree {G : Graph V} {v} : leaf G v = true ↔ degree G v = 1 := by
  simp [leaf]

theorem support_has_leaf {G : Graph V} {v} (h : support G v = true) :
    ∃ w, Adj G v w ∧ leaf G w = true := by
  obtain ⟨w,hw⟩ := positive_member (of_decide_eq_true h)
  exact ⟨w,mem_nbrs.mp hw⟩

theorem leaf_unique_neighbor {G : Graph V} {v w z}
    (h : leaf G v = true) (hw : Adj G v w) (hz : Adj G v z) : w = z := by
  have hv : (nbrs G (fun _ => true) v).length = 1 := leaf_degree.mp h
  have hle : (nbrs G (fun _ => true) v).length ≤ 1 := by omega
  exact singleton_unique hle
    (mem_nbrs.mpr ⟨hw,rfl⟩) (mem_nbrs.mpr ⟨hz,rfl⟩)

theorem walk_has_first {G : Graph V} {v w} (h : Walk G v w) (hne : v ≠ w) :
    ∃ z, Adj G v z := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons e _ => exact ⟨_,e⟩

theorem degree_pos {G : Graph V} (hcon : Connected G) (hn : 3 < G.verts.length) (v : V) :
    0 < degree G v := by
  obtain ⟨x,_,y,_,hxy⟩ := two_members G.nodup (by omega)
  have hother : ∃ w, v ≠ w := by
    by_cases e : v=x
    · exact ⟨y,e ▸ hxy⟩
    · exact ⟨x,e⟩
  obtain ⟨w,hw⟩ := hother
  obtain ⟨z,hz⟩ := walk_has_first (hcon v w) hw
  exact member_positive (mem_nbrs.mpr ⟨hz,rfl⟩)

theorem leaf_pair_traps_walk {G : Graph V} {x y v w}
    (hx : leaf G x = true) (hy : leaf G y = true) (hxy : Adj G x y)
    (hw : Walk G v w) (hv : v=x ∨ v=y) : w=x ∨ w=y := by
  induction hw with
  | nil => exact hv
  | cons e _ ih =>
    apply ih
    rcases hv with rfl|rfl
    · exact Or.inr (leaf_unique_neighbor hx e hxy)
    · exact Or.inl (leaf_unique_neighbor hy e (G.symm _ _ hxy))

theorem leaf_not_support {G : Graph V} (hcon : Connected G)
    (hn : 3 < G.verts.length) {v} (hl : leaf G v = true) : support G v = false := by
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨w,hvw,hw⟩ := support_has_leaf hs
  have hne : v ≠ w := by
    intro e; subst w
    have he := G.loopless v
    simp [Adj,he] at hvw
  have hall : G.verts ⊆ [v,w] := by
    intro z _
    have hh := leaf_pair_traps_walk hl hw hvw (hcon v z) (Or.inl rfl)
    simpa using hh
  have hsmall := subset_le_length G.nodup (by simp [List.nodup_cons,hne]) hall
  simp at hsmall
  omega

theorem minimum_eq_leaf {G : Graph V} (hcon : Connected G) (hn : 3 < G.verts.length)
    (hw : ∃ w, leaf G w = true) (v : V) : minimumDegreeSet G v = leaf G v := by
  obtain ⟨w,hw⟩ := hw
  have hp : ∀ z, 0 < degree G z := degree_pos hcon hn
  have hd : degree G w = 1 := leaf_degree.mp hw
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hvw : degree G v ≤ degree G w := of_decide_eq_true ((List.all_eq_true.mp h) w (G.complete _))
    exact leaf_degree.mpr (by have := hp v; omega)
  · intro h
    have hv : degree G v = 1 := leaf_degree.mp h
    apply List.all_eq_true.mpr
    intro z _
    have := hp z
    exact decide_eq_true (by omega)

theorem exactOneLeaf_private {G : Graph V} {v} (hmin : ∀ u, minimumDegreeSet G u = leaf G u)
    (h : (leafNeighbors G v).length = 1) :
    privateNeighbor G (minimumDegreeSet G) v = true := by
  have e : minimumDegreeSet G = leaf G := funext hmin
  rw [e]
  exact decide_eq_true h

theorem many_leaves_excluded {G : Graph V} {I : V → Bool} {v}
    (hI : TwoIndependent G I) (hsel : I v = true) (h : 2 ≤ (leafNeighbors G v).length) :
    ∃ w, Adj G v w ∧ leaf G w = true ∧ I w = false := by
  have Hnodup : (leafNeighbors G v).Nodup := filter_nodup G.nodup _
  obtain ⟨x,hx,y,hy,hxy⟩ := two_members Hnodup h
  have hx' := mem_nbrs.mp hx
  have hy' := mem_nbrs.mp hy
  cases he : I x with
  | false => exact ⟨x,hx'.1,hx'.2,he⟩
  | true =>
    have hyF : I y = false := by
      apply Bool.eq_false_iff.mpr
      intro hyT
      exact hxy (singleton_unique (hI v hsel)
        (mem_nbrs.mpr ⟨hx'.1,he⟩) (mem_nbrs.mpr ⟨hy'.1,hyT⟩))
    exact ⟨y,hy'.1,hy'.2,hyF⟩

/-- Exact #446, proved pointwise for every 2-independent set. In particular,
it bounds the largest such set by pN(A)+|V∖S|. -/
theorem conjecture446 (G : Graph V) (hcon : Connected G)
    (hn : 3 < G.verts.length) (I : V → Bool) (hI : TwoIndependent G I) :
    cardinal G I ≤ cardinal G (privateNeighbor G (minimumDegreeSet G))
       + cardinal G (fun v => !support G v) := by
  let S := support G
  let A := minimumDegreeSet G
  let P := privateNeighbor G A
  let Q : V → Bool := fun v => decide ((leafNeighbors G v).length = 1)
  let B : V → Bool := fun v => I v && S v
  let Xin : List V := G.verts.filter B
  let Xgood : List V := G.verts.filter (fun v => B v && Q v)
  let Xbad : List V := G.verts.filter (fun v => B v && !Q v)
  let Out : List V := G.verts.filter (fun v => !S v)
  let OutI : List V := G.verts.filter (fun v => I v && !S v)
  let OutNotI : List V := G.verts.filter (fun v => !I v && !S v)
  have hIpart : cardinal G I = Xin.length + OutI.length :=
    count_filter_split G.verts I S
  have hPart : Xin.length = Xgood.length + Xbad.length :=
    count_filter_split G.verts B Q
  have hOut : Out.length = OutI.length + OutNotI.length := by
    have ht := count_filter_split G.verts (fun v => !S v) I
    rw [count_filter_comm, count_filter_comm G.verts (fun v => !S v) (fun v => !I v)] at ht
    exact ht
  have hGood : Xgood.length ≤ cardinal G P := by
    apply subset_le_length (filter_nodup G.nodup _) (filter_nodup G.nodup _)
    intro v hv
    have hvg := List.mem_filter.mp hv
    have hgg := (Bool.and_eq_true _ _).mp hvg.2
    have hvSup := ((Bool.and_eq_true _ _).mp hgg.1).2
    obtain ⟨w,_,hwl⟩ := support_has_leaf hvSup
    apply List.mem_filter.mpr
    exact ⟨hvg.1,exactOneLeaf_private (minimum_eq_leaf hcon hn ⟨w,hwl⟩)
      (of_decide_eq_true hgg.2)⟩
  have hBad : Xbad.length ≤ OutNotI.length := by
    let R : V → V → Prop := fun v w => Adj G v w ∧ leaf G w = true
    apply choose_le_length Xbad OutNotI R
      (filter_nodup G.nodup _) (filter_nodup G.nodup _)
    · intro v hv
      have hvg := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hv).2
      have hIvs := (Bool.and_eq_true _ _).mp hvg.1
      have hpos : 0 < (leafNeighbors G v).length := of_decide_eq_true hIvs.2
      have hne : (leafNeighbors G v).length ≠ 1 := by
        intro he
        have hh : Q v = true := decide_eq_true he
        simp [hh] at hvg
      obtain ⟨w,hvw,hwl,hwI⟩ := many_leaves_excluded hI hIvs.1 (by omega)
      have hwns := leaf_not_support hcon hn hwl
      have hwne : w ∈ OutNotI := List.mem_filter.mpr ⟨G.complete w, by simp [hwI,S,hwns]⟩
      exact ⟨w,hwne,hvw,hwl⟩
    · intro v v' w h1 h2
      exact leaf_unique_neighbor h1.2 (G.symm _ _ h1.1) (G.symm _ _ h2.1)
  change cardinal G I ≤ cardinal G P + Out.length
  omega

#print axioms conjecture446
end Graffiti446
