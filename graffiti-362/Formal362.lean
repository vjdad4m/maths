import Std
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti361
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

theorem degree_pos {G : Graph V} (hcon : Connected G) (hn : 2 < G.verts.length) (v : V) :
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
    (hn : 2 < G.verts.length) {v} (hl : leaf G v = true) : support G v = false := by
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


/-- A simple path recorded by the successive vertices after its start. -/
inductive PathTo (G : Graph V) : V → List V → V → Prop
  | nil {u} : PathTo G u [] u
  | cons {u x v p} : Adj G u x → u ∉ x :: p →
      PathTo G x p v → PathTo G u (x :: p) v

theorem path_single {G : Graph V} {u v} (h : Adj G u v) : PathTo G u [v] v := by
  apply PathTo.cons h _ PathTo.nil
  intro hd
  have he : u = v := by simpa using hd
  subst v
  have hh := G.loopless u
  simp [Adj,hh] at h

theorem path_nodup {G : Graph V} {u p v} (h : PathTo G u p v) :
    (u::p).Nodup := by
  induction h with
  | nil => simp
  | cons _ h _ ih => exact List.nodup_cons.mpr ⟨h,ih⟩

theorem path_endpoint {G : Graph V} {u p v} (h : PathTo G u p v) : v ∈ u::p := by
  induction h with
  | nil => simp
  | cons _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem path_endpoint_tail {G : Graph V} {u p v} (h : PathTo G u p v) (hne : u≠v) :
    v ∈ p := by
  have hm := path_endpoint h
  exact (List.mem_cons.mp hm).resolve_left (fun he => hne he.symm)

theorem path_empty_endpoint {G : Graph V} {u v} (h : PathTo G u [] v) : u=v := by
  cases h
  rfl

theorem path_to_walk {G : Graph V} {u p v} (h : PathTo G u p v) : Walk G u v := by
  induction h with
  | nil => exact .nil
  | cons e _ _ ih => exact .cons e ih

theorem path_append {G : Graph V} {u p v q w}
    (h : PathTo G u p v) (h' : PathTo G v q w)
    (hd : ∀ t ∈ u::p, t ∉ q) : PathTo G u (p++q) w := by
  induction h with
  | nil => exact h'
  | @cons a x b ps he hu hps ih =>
    apply PathTo.cons he
    · intro hh
      have hh' : a ∈ (x::ps) ++ q := hh
      rcases List.mem_append.mp hh' with hpre|hpost
      · exact hu hpre
      · exact hd a (List.mem_cons_self ..) hpost
    · exact ih h' (fun t ht => hd t (List.mem_cons_of_mem _ ht))

theorem path_reverse {G : Graph V} {u p v} (h : PathTo G u p v) :
    ∃ q, PathTo G v q u ∧ q.length = p.length ∧ ∀ a∈v::q, a∈u::p := by
  induction h with
  | nil => exact ⟨[],.nil,rfl,fun _ h => h⟩
  | @cons a x b ps he hu hps ih =>
    obtain ⟨q,hq,hlen,hsub⟩ := ih
    refine ⟨q++[a],path_append hq (path_single (G.symm _ _ he)) ?_, ?_, ?_⟩
    · intro z hz hm
      have heq : z=a := by simpa using hm
      subst z
      exact hu (hsub _ hz)
    · simp [hlen]
    · intro t ht
      have hmem : t∈(b::q) ++ [a] := ht
      rcases List.mem_append.mp hmem with hmem|hmem
      · exact List.mem_cons_of_mem _ (hsub t hmem)
      · have heq : t=a := by simpa using hmem
        subst t
        simp

theorem path_prefix {G : Graph V} {u p v} (h : PathTo G u p v) {w}
    (hw : w ∈ u::p) : ∃ pre suf, p = pre ++ suf ∧ PathTo G u pre w := by
  induction h with
  | @nil a =>
    have heq : w=a := by simpa using hw
    subst w
    exact ⟨[],[],rfl,.nil⟩
  | @cons a x b ps he hu hps ih =>
    rcases List.mem_cons.mp hw with e|hw'
    · subst w; exact ⟨[],x::ps,rfl,.nil⟩
    · obtain ⟨pre,suf,hcat,hroute⟩ := ih hw'
      refine ⟨x::pre,suf,by simp [hcat],PathTo.cons he ?_ hroute⟩
      intro hmem
      apply hu
      rw [hcat]
      exact List.mem_append_left suf hmem

/-- The classical unique-simple-path presentation of a finite tree. This is
equivalent to a connected undirected simple graph with no cycle. -/
structure Tree (V : Type u) where
  graph : Graph V
  existsPath : ∀ a b : V, ∃ p, PathTo graph a p b
  uniquePath : ∀ a b p q, PathTo graph a p b → PathTo graph a q b → p=q

def TPath (T : Tree V) := PathTo T.graph

noncomputable def chosen (T : Tree V) (a b : V) : List V :=
  Classical.choose (T.existsPath a b)

theorem chosen_path (T : Tree V) (a b : V) : TPath T a (chosen T a b) b :=
  Classical.choose_spec (T.existsPath a b)

theorem tree_connected (T : Tree V) : Connected T.graph := fun a b =>
  path_to_walk (chosen_path T a b)

noncomputable def dist (T : Tree V) (a b : V) : Nat := (chosen T a b).length

theorem dist_eq {T : Tree V} {a p b} (h : TPath T a p b) : dist T a b = p.length := by
  unfold dist
  rw [T.uniquePath _ _ _ _ (chosen_path T _ _) h]

theorem dist_self (T : Tree V) (a : V) : dist T a a = 0 :=
  dist_eq (PathTo.nil : TPath T a [] a)

theorem dist_adj {T : Tree V} {a b} (h : Adj T.graph a b) : dist T a b = 1 :=
  dist_eq (path_single h)

theorem dist_pos {T : Tree V} {a b} (h : a≠b) : 0 < dist T a b := by
  unfold dist
  cases he : chosen T a b with
  | nil =>
    have hi := chosen_path T a b
    rw [he] at hi
    exact False.elim (h (path_empty_endpoint hi))
  | cons x xs => simp

theorem path_different_branches_disjoint {T : Tree V} {u z z' p q a b}
    (hp : TPath T u (z::p) a) (hq : TPath T u (z'::q) b) (hd : z≠z') :
    ∀ w ∈ z::p, w ∉ z'::q := by
  intro w hw hw'
  obtain ⟨pre,suf,hcat,hroute⟩ := path_prefix hp (List.mem_cons_of_mem _ hw)
  obtain ⟨pre',suf',hcat',hroute'⟩ := path_prefix hq (List.mem_cons_of_mem _ hw')
  have he := T.uniquePath _ _ _ _ hroute hroute'
  have hn := (List.nodup_cons.mp (path_nodup hp)).1
  cases hne : pre with
  | nil =>
    rw [hne] at hroute
    have heq := path_empty_endpoint hroute
    subst w
    exact hn hw
  | cons x xs =>
    have heq : z=x := by
      rw [hne] at hcat
      exact (List.cons.inj hcat).1
    rw [← he,hne] at hcat'
    have heq' : z'=x := (List.cons.inj hcat').1
    exact hd (heq.trans heq'.symm)

theorem path_starts_iff_contains_neighbor {T : Tree V} {u z p v}
    (e : Adj T.graph u z) (h : TPath T u p v) (hz : z ∈ p) :
    ∃ q, p = z::q := by
  obtain ⟨pre,suf,hp,hroute⟩ := path_prefix h (List.mem_cons_of_mem _ hz)
  have he := T.uniquePath _ _ _ _ hroute (path_single e)
  rw [he] at hp
  exact ⟨suf,hp⟩

theorem dist_other_branch {T : Tree V} {u z p v x}
    (h : TPath T u (z::p) v)
    (hx : z ∉ chosen T u x) : dist T v x = dist T v u + dist T u x := by
  obtain ⟨q,hq,_,hsub⟩ := path_reverse h
  have hux := chosen_path T u x
  have hdis : ∀ a∈v::q, a∉chosen T u x := by
    intro a ha ham
    have has := hsub a ha
    rcases List.mem_cons.mp has with he|hahas
    · subst a
      exact (List.nodup_cons.mp (path_nodup hux)).1 ham
    · cases hcomp : chosen T u x with
      | nil => rw [hcomp] at ham; contradiction
      | cons w ws =>
        have hh := hux
        rw [hcomp] at hh
        have hzw : z≠w := by
          intro e; subst w
          apply hx; rw [hcomp]; simp
        exact path_different_branches_disjoint h hh hzw _ hahas (hcomp ▸ ham)
  have he := dist_eq (path_append hq hux hdis)
  rw [List.length_append, ← dist_eq hq] at he
  exact he

def maxList (xs : List Nat) : Nat := xs.foldr max 0

theorem maxList_upper {xs : List Nat} {x : Nat} (h : x∈xs) : x≤maxList xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp h with e|h
    · subst x; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxList_attains {xs : List Nat} (h : xs≠[]) : maxList xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => simp [maxList]
    | cons b bs =>
      have hf := ih (by simp)
      change max a (maxList (b::bs)) ∈ a::b::bs
      by_cases he : a ≤ maxList (b::bs)
      · rw [Nat.max_eq_right he]
        exact List.mem_cons_of_mem _ hf
      · rw [Nat.max_eq_left (by omega)]
        simp

noncomputable def eccentricity (T : Tree V) (v : V) : Nat :=
  maxList (T.graph.verts.map (dist T v))

noncomputable def center (T : Tree V) (v : V) : Bool :=
  T.graph.verts.all (fun w => decide (eccentricity T v ≤ eccentricity T w))

theorem ecc_upper (T : Tree V) (v w : V) : dist T v w ≤ eccentricity T v := by
  unfold eccentricity
  exact maxList_upper (List.mem_map.mpr ⟨w,T.graph.complete _,rfl⟩)

theorem ecc_attains (T : Tree V) (v : V) : ∃ w, dist T v w = eccentricity T v := by
  have hn : T.graph.verts.map (dist T v) ≠ [] := by
    intro he
    have he' : dist T v v ∈ T.graph.verts.map (dist T v) :=
      List.mem_map.mpr ⟨v,T.graph.complete _,rfl⟩
    rw [he] at he'; contradiction
  obtain ⟨w,_,hw⟩ := List.mem_map.mp (maxList_attains hn)
  exact ⟨w,hw⟩

theorem center_char {T : Tree V} {v} : center T v = true ↔
    ∀ w, eccentricity T v ≤ eccentricity T w := by
  unfold center
  simp [List.all_eq_true,T.graph.complete]

theorem dist_symm (T : Tree V) (a b : V) : dist T a b = dist T b a := by
  obtain ⟨q,hq,hqLen,_⟩ := path_reverse (chosen_path T a b)
  rw [dist_eq hq,hqLen]
  rfl

theorem distStep {T : Tree V} {u v w} (e : Adj T.graph u v) :
    dist T u w ≤ 1 + dist T v w := by
  by_cases hv : v ∈ chosen T u w
  · obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor e (chosen_path T u w) hv
    have hp := chosen_path T u w
    rw [hq] at hp
    have htail : TPath T v q w := by cases hp with | cons _ _ h => exact h
    rw [dist_eq hp, dist_eq htail]
    simp [Nat.add_comm]
  · have he := dist_other_branch (path_single e) hv
    rw [dist_adj (T.graph.symm _ _ e)] at he
    omega

theorem distPathTriangle {T : Tree V} {u v p} (hp : TPath T u p v) (w : V) :
    dist T u w ≤ p.length + dist T v w := by
  induction hp with
  | nil => simp
  | @cons u z v p he _ h ih =>
    have hs := distStep (w:=w) he
    simp only [List.length_cons]
    omega

theorem distTriangle (T : Tree V) (u v w : V) :
    dist T u w ≤ dist T u v + dist T v w :=
  distPathTriangle (chosen_path T u v) w

noncomputable def radius (T : Tree V) : Nat :=
  T.graph.verts.foldr (fun u r => min (eccentricity T u) r)
    (maxList (T.graph.verts.map (eccentricity T)))

theorem radiusAttains (T : Tree V) (h : 0 < T.graph.verts.length) :
    (∃ u, eccentricity T u = radius T) ∧ ∀ u, radius T ≤ eccentricity T u := by
  let m := maxList (T.graph.verts.map (eccentricity T))
  have allLe : ∀ u, eccentricity T u ≤ m :=
    fun u => maxList_upper (List.mem_map.mpr ⟨u,T.graph.complete _,rfl⟩)
  have aux : ∀ l : List V, ∀ {a : Nat} (ha : ∃ u, eccentricity T u = a),
      (∃ u, eccentricity T u = l.foldr (fun u r => min (eccentricity T u) r) a) ∧
      (∀ u ∈ l, l.foldr (fun u r => min (eccentricity T u) r) a ≤ eccentricity T u) := by
    intro l
    induction l with
    | nil => intro a ha; exact ⟨ha, by simp⟩
    | cons v l ih =>
      intro a ha
      obtain ⟨⟨w,hw⟩,hb⟩ := ih ha
      constructor
      · by_cases hv : eccentricity T v ≤ l.foldr (fun u r => min (eccentricity T u) r) a
        · exact ⟨v,(Nat.min_eq_left hv).symm⟩
        · exact ⟨w,hw.trans (Nat.min_eq_right (by omega)).symm⟩
      · intro u hu
        cases List.mem_cons.mp hu with
        | inl e => subst u; exact Nat.min_le_left _ _
        | inr e => exact Nat.le_trans (Nat.min_le_right _ _) (hb _ e)
  have hv : T.graph.verts.map (eccentricity T) ≠ [] := by
    obtain ⟨u,hu⟩ := positive_member h
    have hx : eccentricity T u ∈ T.graph.verts.map (eccentricity T) := List.mem_map.mpr ⟨u,hu,rfl⟩
    intro e
    rw [e] at hx
    exact List.not_mem_nil hx
  obtain ⟨u,_,hu⟩ := List.mem_map.mp (maxList_attains hv)
  obtain ⟨he,hp⟩ := aux T.graph.verts ⟨u,hu⟩
  exact ⟨he,fun u => hp u (T.graph.complete u)⟩

theorem longPath (T : Tree V) (h : 0 < T.graph.verts.length) (hr : 0 < radius T) :
    ∃ a b p, TPath T a p b ∧ 2*radius T ≤ p.length+1 := by
  obtain ⟨⟨u,hu⟩,hmin⟩ := radiusAttains T h
  obtain ⟨a,ha⟩ := ecc_attains T u
  have hp := chosen_path T u a
  cases hpa : chosen T u a with
  | nil =>
    have he : dist T u a = 0 := by simp [dist,hpa]
    omega
  | cons z p =>
    rw [hpa] at hp
    have hz : Adj T.graph u z := by cases hp with | cons e _ _ => exact e
    obtain ⟨b,hb⟩ := ecc_attains T z
    have hbase := hmin z
    have haway : z ∉ chosen T u b := by
      intro hzmem
      obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor hz (chosen_path T u b) hzmem
      have hw := chosen_path T u b
      rw [hq] at hw
      have htail : TPath T z q b := by cases hw with | cons _ _ hh => exact hh
      have h1 := dist_eq hw
      have h2 := dist_eq htail
      have h3 := ecc_upper T u b
      simp only [List.length_cons] at h1
      omega
    have hfar := dist_other_branch hp haway
    have e0 := distStep (w:=b) (T.graph.symm _ _ hz)
    have e1 := dist_symm T a u
    have e2 : dist T a b = (chosen T a b).length := rfl
    exact ⟨a,b,chosen T a b,chosen_path T a b,by omega⟩

theorem choose_le_length_other {W : Type u} [DecidableEq W] (xs : List V) (ys : List W) (R : V → W → Prop)
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


theorem endpoint_unique {G : Graph V} {a b p} (h : PathTo G a p b)
    {c} (h' : PathTo G a p c) : b = c := by
  induction h with
  | nil => cases h'; rfl
  | cons _ _ _ ih =>
    cases h' with | cons _ _ hp => exact ih hp

theorem path_dist_labels {T : Tree V} {a b p} (h : TPath T a p b)
    {u v} (hu : u ∈ a::p) (hv : v ∈ a::p)
    (he : dist T a u = dist T a v) : u = v := by
  obtain ⟨l,m,hl,hL⟩ := path_prefix h hu
  obtain ⟨q,r,hq,hQ⟩ := path_prefix h hv
  have hlen : l.length = q.length := (dist_eq hL).symm.trans (he.trans (dist_eq hQ))
  have le : p.take l.length = l := by rw [hl, List.take_left]
  have qe : p.take q.length = q := by rw [hq, List.take_left]
  have hlq : l = q := le.symm.trans (hlen ▸ qe)
  exact endpoint_unique hL (hlq ▸ hQ)

def slots (ds : List V) : List (V × Nat) :=
  ds.flatMap (fun d => (List.range 5).map (fun j => (d,j)))

theorem slots_mem (ds : List V) (d : V) (j : Nat) (hd : d ∈ ds) (hj : j < 5) :
    (d,j) ∈ slots ds :=
  List.mem_flatMap.mpr ⟨d,hd,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩⟩

theorem slots_length (ds : List V) : (slots ds).length = 5 * ds.length := by
  induction ds with
  | nil => simp [slots]
  | cons a ds ih =>
    change (((List.range 5).map (fun j => (a,j))) ++ slots ds).length = _
    simp only [List.length_append,List.length_map,List.length_range,ih,List.length_cons]
    omega

theorem slots_nodup {ds : List V} (hn : ds.Nodup) : (slots ds).Nodup := by
  induction ds with
  | nil => simp [slots]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hn
    change (((List.range 5).map (fun j => (a,j))) ++ slots l).Nodup
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr (List.Pairwise.imp ?_ List.nodup_range),ih hl,?_⟩
    · intro x y hxy he
      exact hxy (congrArg Prod.snd he)
    · intro x hx y hy he
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨b,hb,hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hy
      have hba : a=b := congrArg Prod.fst he
      exact ha (hba.symm ▸ hb)

theorem pack_path {T : Tree V} {a b p} (hp : TPath T a p b) (ds : List V) (hd : ds.Nodup)
    (hc : ∀ x, ∃ d ∈ ds, dist T x d ≤ 2) : p.length+1 ≤ 5*ds.length := by
  let R : V → (V × Nat) → Prop :=
    fun x s => x∈a::p ∧ dist T a x + 2 = s.2 + dist T a s.1
  have hh : ∀ x ∈ a::p, ∃ s ∈ slots ds, R x s := by
    intro x hx
    obtain ⟨d,hd,hxd⟩ := hc x
    have h1 := distTriangle T a x d
    have h2 := distTriangle T a d x
    rw [← dist_symm T x d] at h2
    let j := dist T a x + 2 - dist T a d
    have hj : j < 5 := by dsimp [j]; omega
    refine ⟨(d,j),slots_mem ds d j hd hj,hx,?_⟩
    dsimp [j]
    omega
  have inj : ∀ x x' s, R x s → R x' s → x = x' := by
    intro x x' s h1 h2
    apply path_dist_labels hp h1.1 h2.1
    have h11 := h1.2
    have h22 := h2.2
    omega
  have le := choose_le_length_other (a::p) (slots ds) R (path_nodup hp) (slots_nodup hd) hh inj
  simpa [slots_length] using le

def TotalDominating (G : Graph V) (D : V → Bool) : Prop :=
  ∀ v, ∃ w, Adj G v w ∧ D w = true

theorem adj_ne {G : Graph V} {v w} (h : Adj G v w) : v ≠ w := by
  intro he
  subst w
  have hl := G.loopless v
  simp [Adj,hl] at h

theorem supports_in_total {G : Graph V} {D : V → Bool} (hD : TotalDominating G D)
    {s} (hs : support G s = true) : D s = true := by
  obtain ⟨w,hsw,hwl⟩ := support_has_leaf hs
  obtain ⟨b,hwb,hb⟩ := hD w
  have he := leaf_unique_neighbor hwl hwb (G.symm _ _ hsw)
  rwa [he] at hb

theorem hasMinAux {P : Nat → Prop} (n : Nat) (h : ∃ k, k≤n ∧ P k) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  induction n with
  | zero =>
    obtain ⟨k,hk,hp⟩ := h
    have e : k=0 := by omega
    subst k
    exact ⟨0,hp,fun _ _ => Nat.zero_le _⟩
  | succ n ih =>
    by_cases he : ∃ k, k≤n ∧ P k
    · exact ih he
    · obtain ⟨k,hk,hp⟩ := h
      have hnk : ¬ k≤n := fun h' => he ⟨k,h',hp⟩
      have ek : k=n+1 := by omega
      subst k
      refine ⟨n+1,hp,?_⟩
      intro m hm
      have hnm : ¬ m≤n := fun h' => he ⟨m,h',hm⟩
      omega

def AttainableTotal (G : Graph V) (m : Nat) : Prop :=
  ∃ D : V → Bool, TotalDominating G D ∧ cardinal G D = m

theorem hasMinTotal (T : Tree V) (hn : 2 < T.graph.verts.length) :
    ∃ m, AttainableTotal T.graph m ∧ ∀ k, AttainableTotal T.graph k → m ≤ k := by
  apply hasMinAux T.graph.verts.length
  let D : V → Bool := fun _ => true
  refine ⟨cardinal T.graph D,List.length_filter_le _ _,D,?_,rfl⟩
  intro v
  obtain ⟨w,hw⟩ := positive_member (degree_pos (tree_connected T) hn v)
  exact ⟨w,(mem_nbrs.mp hw).1,rfl⟩

/-- The order of a minimum total dominating set. -/
noncomputable def totalDominationNumber (T : Tree V) (hn : 2 < T.graph.verts.length) : Nat :=
  Classical.choose (hasMinTotal T hn)


/-- A class-transversal for an equivalence relation on vertices present in a list. -/
structure CRReps (r : V → V → Prop) (xs reps : List V) : Prop where
  nodup : reps.Nodup
  sub : reps ⊆ xs
  cover : ∀ x ∈ xs, ∃ y ∈ reps, r x y
  unique : ∀ x ∈ reps, ∀ y ∈ reps, r x y → x = y

/-- Greedily choose exactly one representative per class. -/
noncomputable def crGreedy (r : V → V → Prop) : List V → List V
  | [] => []
  | x :: xs => by
    classical
    exact if ∃ y ∈ crGreedy r xs, r x y then crGreedy r xs else x :: crGreedy r xs

theorem crGreedy_spec (r : V → V → Prop) (hr : Equivalence r) (xs : List V) :
    CRReps r xs (crGreedy r xs) := by
  classical
  induction xs with
  | nil => exact ⟨by simp [crGreedy], by simp [crGreedy], by simp [crGreedy], by simp [crGreedy]⟩
  | cons x xs ih =>
    rw [crGreedy]
    split
    · rename_i hhead
      refine ⟨ih.nodup, fun y hy => List.mem_cons_of_mem _ (ih.sub hy), ?_, ih.unique⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hhead
      · exact ih.cover y hy
    · rename_i hhead
      have hx : x ∉ crGreedy r xs := fun hm => hhead ⟨x,hm,hr.refl x⟩
      refine ⟨List.nodup_cons.mpr ⟨hx,ih.nodup⟩, ?_, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · exact List.mem_cons_of_mem _ (ih.sub hy)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨_,List.mem_cons_self ..,hr.refl _⟩
        · obtain ⟨z,hz,hyz⟩ := ih.cover y hy
          exact ⟨z,List.mem_cons_of_mem _ hz,hyz⟩
      · intro a ha b hb hab
        rcases List.mem_cons.mp ha with ea | ha'
        · subst a
          rcases List.mem_cons.mp hb with eb | hb'
          · exact eb.symm
          · exact False.elim (hhead ⟨b,hb',hab⟩)
        · rcases List.mem_cons.mp hb with eb | hb'
          · subst b
            exact False.elim (hhead ⟨a,ha',hr.symm hab⟩)
          · exact ih.unique a ha' b hb' hab

/-- All complete duplicate-free class-transversals have the same length. -/
theorem crCard_eq (r : V → V → Prop) (hr : Equivalence r)
    {xs ls rs : List V} (hl : CRReps r xs ls) (hR : CRReps r xs rs) :
    ls.length = rs.length := by
  let p (a b : V) := a ∈ ls ∧ r a b
  have hlr : ls.length ≤ rs.length := by
    apply choose_le_length ls rs p hl.nodup hR.nodup
    · intro a ha
      obtain ⟨b,hb,hab⟩ := hR.cover a (hl.sub ha)
      exact ⟨b,hb,ha,hab⟩
    · intro a a' b hab ha'b
      exact hl.unique a hab.1 a' ha'b.1 (hr.trans hab.2 (hr.symm ha'b.2))
  let q (a b : V) := a ∈ rs ∧ r a b
  have hrl : rs.length ≤ ls.length := by
    apply choose_le_length rs ls q hR.nodup hl.nodup
    · intro a ha
      obtain ⟨b,hb,hab⟩ := hl.cover a (hR.sub ha)
      exact ⟨b,hb,ha,hab⟩
    · intro a a' b hab ha'b
      exact hR.unique a hab.1 a' ha'b.1 (hr.trans hab.2 (hr.symm ha'b.2))
  exact Nat.le_antisymm hlr hrl

theorem crWalk_append {G : Graph V} {u v w : V}
    (p : Walk G u v) (q : Walk G v w) : Walk G u w := by
  induction p with
  | nil => exact q
  | cons e _ ih => exact Walk.cons e (ih q)

theorem crWalk_reverse {G : Graph V} {u v : V}
    (p : Walk G u v) : Walk G v u := by
  induction p with
  | nil => exact Walk.nil
  | cons e _ ih => exact crWalk_append ih (Walk.cons (G.symm _ _ e) Walk.nil)

theorem crWalk_equiv (G : Graph V) : Equivalence (Walk G) :=
  ⟨fun _ => Walk.nil, crWalk_reverse, crWalk_append⟩

/-- The induced subgraph, represented on the ambient vertices with all
out-of-predicate vertices isolated. Components are counted only inside P. -/
def crInduced (G : Graph V) (P : V → Bool) : Graph V where
  verts := G.verts
  nodup := G.nodup
  complete := G.complete
  edge x y := P x && P y && G.edge x y
  symm x y h := by
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.2,h.1.1⟩,G.symm x y h.2⟩
  loopless x := by simp [G.loopless]

theorem crInduced_step {G : Graph V} {P : V → Bool} {x y : V}
    (hx : P x = true) (hy : P y = true) (h : Adj G x y) :
    Walk (crInduced G P) x y :=
  Walk.cons (by simpa [Adj, crInduced, hx, hy] using h) Walk.nil

/-- The exact induced component count, represented by any class-transversal.
Its independence of the chosen transversal is proved in crCard_eq. -/
noncomputable def crComponentCount (G : Graph V) (P : V → Bool) : Nat :=
  (crGreedy (Walk (crInduced G P)) (G.verts.filter P)).length

/-- For a prescribed subset Q meeting every induced component of P, choose
one vertex of Q per component. The selected vertices are independent in G;
the list's length equals the full induced component count of P. -/
theorem crChooseSubset (G : Graph V) (P Q : V → Bool)
    (hsub : ∀ v, Q v = true → P v = true)
    (hmeet : ∀ v, P v = true → ∃ w, Q w = true ∧ Walk (crInduced G P) v w) :
    ∃ rs : List V, rs.Nodup ∧ (∀ v ∈ rs, Q v = true) ∧
      (∀ v ∈ rs, ∀ w ∈ rs, ¬ Adj G v w) ∧ rs.length = crComponentCount G P := by
  let g := crInduced G P
  let rs := crGreedy (Walk g) (G.verts.filter Q)
  have he := crWalk_equiv g
  have hr : CRReps (Walk g) (G.verts.filter Q) rs := crGreedy_spec _ he _
  have hall : CRReps (Walk g) (G.verts.filter P) rs := by
    refine ⟨hr.nodup, ?_, ?_, hr.unique⟩
    · intro y hy
      have hq := (List.mem_filter.mp (hr.sub hy)).2
      exact List.mem_filter.mpr ⟨G.complete y,hsub y hq⟩
    · intro v hv
      obtain ⟨w,hw,hwlk⟩ := hmeet v (List.mem_filter.mp hv).2
      obtain ⟨z,hz,hwz⟩ := hr.cover w (List.mem_filter.mpr ⟨G.complete w,hw⟩)
      exact ⟨z,hz,crWalk_append hwlk hwz⟩
  refine ⟨rs,hr.nodup,fun v hv => (List.mem_filter.mp (hr.sub hv)).2,?_,?_⟩
  · intro v hv w hw e
    have hpv := hsub v (List.mem_filter.mp (hr.sub hv)).2
    have hpw := hsub w (List.mem_filter.mp (hr.sub hw)).2
    have heq := hr.unique v hv w hw (crInduced_step hpv hpw e)
    subst w
    have hh := G.loopless v
    simp [Adj,hh] at e
  · exact crCard_eq _ he hall (crGreedy_spec _ he _)

def crLeafSupport (G : Graph V) (v : V) : Bool := support G v || leaf G v

theorem crSupportRepresentatives (G : Graph V) :
    ∃ rs : List V, rs.Nodup ∧ (∀ v ∈ rs, support G v = true) ∧
      (∀ v ∈ rs, ∀ w ∈ rs, ¬ Adj G v w) ∧
      rs.length = crComponentCount G (crLeafSupport G) := by
  apply crChooseSubset G (crLeafSupport G) (support G)
  · intro v hv
    simp [crLeafSupport,hv]
  · intro v hv
    rcases Bool.or_eq_true_iff.mp hv with hs | hl
    · exact ⟨v,hs,Walk.nil⟩
    · have hd := leaf_degree.mp hl
      obtain ⟨w,hw⟩ := positive_member (xs := nbrs G (fun _ => true) v)
        (by change 0 < degree G v; omega)
      have e := (mem_nbrs.mp hw).1
      have hrev := G.symm _ _ e
      have hleaf : v ∈ leafNeighbors G w := mem_nbrs.mpr ⟨hrev,hl⟩
      have hsw : support G w = true := decide_eq_true (member_positive hleaf)
      exact ⟨w,hsw,crInduced_step hv (by simp [crLeafSupport,hsw]) e⟩

theorem bound362 (T : Tree V) (hn : 2 < T.graph.verts.length) (D : V → Bool)
    (hD : TotalDominating T.graph D) :
    3*crComponentCount T.graph (crLeafSupport T.graph) + 1 + radius T ≤ 3*cardinal T.graph D := by
  let G := T.graph
  obtain ⟨rs,hnd,hmem,hi,hcount⟩ := crSupportRepresentatives G
  let R : V → Bool := fun v => decide (v ∈ rs)
  let Ds : List V := G.verts.filter (fun v => D v && !(R v))
  have hrD : ∀ v ∈ rs, D v = true := fun v hv => supports_in_total hD (hmem v hv)
  have remaining : ∀ x, ∃ d ∈ Ds, dist T x d ≤ 2 := by
    intro x
    obtain ⟨y,hxy,hyD⟩ := hD x
    by_cases hyr : y ∈ rs
    · obtain ⟨z,hyz,hzD⟩ := hD y
      have hz : z ∉ rs := fun hz => hi y hyr z hz hyz
      have hzd : z ∈ Ds := List.mem_filter.mpr ⟨G.complete z, by simp [R,hzD,hz]⟩
      refine ⟨z,hzd,?_⟩
      have h1 := distTriangle T x y z
      rw [dist_adj hxy,dist_adj hyz] at h1
      omega
    · exact ⟨y,List.mem_filter.mpr ⟨G.complete y,by simp [R,hyD,hyr]⟩,
        by rw [dist_adj hxy]; decide⟩
  have hnonempty : 0 < G.verts.length := by change 0 < T.graph.verts.length; omega
  obtain ⟨x,_⟩ := positive_member hnonempty
  obtain ⟨d,hd,_⟩ := remaining x
  have hpos := member_positive hd
  have coverage : 2*radius T ≤ 5*Ds.length := by
    by_cases hrad : 0 < radius T
    · obtain ⟨a,b,p,hp,hh⟩ := longPath T hnonempty hrad
      have hpack := pack_path hp Ds (filter_nodup G.nodup _) remaining
      omega
    · omega
  have hcard : (G.verts.filter (fun v => D v && R v)).length = rs.length := by
    apply Nat.le_antisymm
    · apply subset_le_length (filter_nodup G.nodup _) hnd
      intro v hv
      obtain ⟨_,h⟩ := List.mem_filter.mp hv
      exact of_decide_eq_true ((Bool.and_eq_true _ _).mp h).2
    · apply subset_le_length hnd (filter_nodup G.nodup _)
      intro v hv
      exact List.mem_filter.mpr ⟨G.complete v,by simp [R,hrD v hv,hv]⟩
  have ht := count_filter_split G.verts D R
  rw [hcard] at ht
  change cardinal G D = rs.length + Ds.length at ht
  change 3*crComponentCount G (crLeafSupport G) + 1 + radius T ≤ 3*cardinal G D
  rw [← hcount,ht]
  omega

/-- Exact integer-scaled form of #362: t ≥ c + (1 + radius)/3. -/
theorem conjecture362_exact (T : Tree V) (hn : 2 < T.graph.verts.length) :
    3*crComponentCount T.graph (crLeafSupport T.graph) + 1 + radius T ≤
      3*totalDominationNumber T hn := by
  obtain ⟨D,hD,hcard⟩ := (Classical.choose_spec (hasMinTotal T hn)).1
  change cardinal T.graph D = totalDominationNumber T hn at hcard
  rw [← hcard]
  exact bound362 T hn D hD

#print axioms conjecture362_exact
end Graffiti361
