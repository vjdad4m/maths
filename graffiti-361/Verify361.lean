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

theorem centers_adjacent {T : Tree V} {u v} (hu : center T u = true)
    (hv : center T v = true) (hneq : u≠v) : Adj T.graph u v := by
  have huv := chosen_path T u v
  cases hcc : chosen T u v with
  | nil =>
    rw [hcc] at huv
    exact False.elim (hneq (path_empty_endpoint huv))
  | cons z p =>
    rw [hcc] at huv
    have he : Adj T.graph u z := by cases huv with | cons e _ _ => exact e
    have hp : TPath T z p v := by cases huv with | cons _ _ hp => exact hp
    cases pp : p with
    | nil =>
      rw [pp] at hp
      rw [path_empty_endpoint hp] at he
      exact he
    | cons z' ps =>
      have hzu : z≠u := by
        intro ee; subst z
        have hh := T.graph.loopless u
        simp [Adj,hh] at he
      obtain ⟨x,hx⟩ := ecc_attains T z
      by_cases hz : z ∈ chosen T u x
      · obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor he (chosen_path T u x) hz
        have hxroute := chosen_path T u x
        rw [hq] at hxroute
        have htail : TPath T z q x := by cases hxroute with | cons _ _ hh => exact hh
        have d1 := dist_eq hxroute
        have d2 := dist_eq htail
        have h1 := ecc_upper T u x
        have h2 := center_char.mp hu z
        simp at d1
        omega
      · have d1 := dist_other_branch huv hz
        have hxroute := chosen_path T u x
        have hnew : TPath T z (u :: chosen T u x) x := by
          apply PathTo.cons (T.graph.symm _ _ he) _ hxroute
          intro hh
          exact (List.mem_cons.mp hh).elim hzu hz
        have d2 := dist_eq hnew
        have d3 := dist_eq huv
        have d4 : dist T v u = dist T u v := by
          obtain ⟨q,hq,hl,_⟩ := path_reverse huv
          rw [dist_eq hq,d3,hl]
        rw [pp] at d3
        have h1 := ecc_upper T v x
        have h2 := center_char.mp hv z
        simp at d2 d3
        have d5 : (chosen T u x).length = dist T u x := rfl
        omega

theorem tree_no_triangle {T : Tree V} {u v w}
    (e : Adj T.graph u v) (f : Adj T.graph v w) (g : Adj T.graph w u) : False := by
  have hn : u ∉ [v,w] := by
    intro h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h
    · subst v; have hh := T.graph.loopless u; simp [Adj,hh] at e
    · subst w; have hh := T.graph.loopless u; simp [Adj,hh] at g
  have hpath : TPath T u [v,w] w := PathTo.cons e hn (path_single f)
  have heq := T.uniquePath _ _ _ _ hpath (path_single (T.graph.symm _ _ g))
  have hh := congrArg List.length heq
  simp at hh

theorem centers_at_most_two (T : Tree V) : cardinal T.graph (center T) ≤ 2 := by
  unfold cardinal
  let cs := T.graph.verts.filter (center T)
  have hd := filter_nodup T.graph.nodup (center T)
  change cs.Nodup at hd
  change cs.length ≤ 2
  cases hcs : cs with
  | nil => simp
  | cons a as =>
    cases has : as with
    | nil => simp
    | cons b bs =>
      cases hbs : bs with
      | nil => simp
      | cons c ls =>
        have hc : ∀ z∈a::b::c::ls, center T z = true := by
          intro z hz
          have hm : z ∈ cs := by rw [hcs,has,hbs]; exact hz
          exact (List.mem_filter.mp hm).2
        rw [hcs,has,hbs] at hd
        have hab : a≠b := fun e => (List.nodup_cons.mp hd).1 (by simp [e])
        have hac : a≠c := fun e => (List.nodup_cons.mp hd).1 (by simp [e])
        have hbc : b≠c := fun e => (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (by simp [e])
        have e := centers_adjacent (hc a (by simp)) (hc b (by simp)) hab
        have f := centers_adjacent (hc b (by simp)) (hc c (by simp)) hbc
        have g := centers_adjacent (hc c (by simp)) (hc a (by simp)) (Ne.symm hac)
        exact False.elim (tree_no_triangle e f g)


def TotalDominating (G : Graph V) (D : V → Bool) : Prop :=
  ∀ v, ∃ w, Adj G v w ∧ D w = true

theorem adj_ne {G : Graph V} {v w} (h : Adj G v w) : v ≠ w := by
  intro he
  subst w
  have hl := G.loopless v
  simp [Adj,hl] at h

theorem card_mono {G : Graph V} {P Q : V → Bool} (h : ∀ v, P v=true → Q v=true) :
    cardinal G P ≤ cardinal G Q := by
  apply subset_le_length (filter_nodup G.nodup _) (filter_nodup G.nodup _)
  intro v hv
  have hm := List.mem_filter.mp hv
  exact List.mem_filter.mpr ⟨hm.1,h _ hm.2⟩

theorem card_eq {G : Graph V} {P Q : V → Bool} (h : ∀ v, P v=true ↔ Q v=true) :
    cardinal G P = cardinal G Q :=
  Nat.le_antisymm (card_mono (fun v => (h v).mp)) (card_mono (fun v => (h v).mpr))

theorem two_members_lower {xs : List V} {u v}
    (hu : u∈xs) (hv : v∈xs) (he : u≠v) : 2 ≤ xs.length := by
  by_cases h : xs.length ≤ 1
  · exact False.elim (he (singleton_unique h hu hv))
  · omega

theorem distinct_third {G : Graph V} (hn : 2 < G.verts.length) {u v : V}
    (hne : u≠v) : ∃ z, z≠u ∧ z≠v := by
  by_cases he : ∃ z, z≠u ∧ z≠v
  · exact he
  · exfalso
    have hd : G.verts ⊆ [u,v] := by
      intro x _
      by_cases hx : x=u
      · simp [hx]
      · by_cases hy : x=v
        · simp [hy]
        · exact False.elim (he ⟨x,hx,hy⟩)
    have h := subset_le_length G.nodup (by simp [hne]) hd
    simp at h
    omega

theorem supports_in_total {G : Graph V} {D : V → Bool} (hD : TotalDominating G D)
    {s} (hs : support G s = true) : D s = true := by
  obtain ⟨w,hsw,hwl⟩ := support_has_leaf hs
  obtain ⟨b,hwb,hb⟩ := hD w
  have he := leaf_unique_neighbor hwl hwb (G.symm _ _ hsw)
  rwa [he] at hb

theorem total_at_least_two {G : Graph V} {D : V → Bool} (hn : 2 < G.verts.length)
    (hD : TotalDominating G D) : 2 ≤ cardinal G D := by
  obtain ⟨v,_⟩ := positive_member (show 0<G.verts.length by omega)
  obtain ⟨x,_,hx⟩ := hD v
  obtain ⟨y,hxy,hy⟩ := hD x
  exact two_members_lower
    (List.mem_filter.mpr ⟨G.complete x,hx⟩)
    (List.mem_filter.mpr ⟨G.complete y,hy⟩) (adj_ne hxy)

def SupportIndependent (G : Graph V) : Prop :=
  ∀ a b, support G a = true → support G b = true → ¬ Adj G a b

def supportIsolate (G : Graph V) (v : V) : Bool :=
  support G v && decide ((nbrs G (support G) v).length = 0)

theorem isolate_char {G : Graph V} {v} :
    supportIsolate G v = true ↔ support G v = true ∧ (nbrs G (support G) v).length = 0 := by
  simp [supportIsolate]

theorem isolates_all_if_independent {G : Graph V} (hi : SupportIndependent G) :
    cardinal G (supportIsolate G) = cardinal G (support G) := by
  apply card_eq
  intro v
  constructor
  · exact fun h => (isolate_char.mp h).1
  · intro h
    apply isolate_char.mpr
    refine ⟨h,?_⟩
    have hh : nbrs G (support G) v = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w _ hw
      obtain ⟨he,hs⟩ := (Bool.and_eq_true _ _).mp hw
      exact hi v w h hs he
    rw [hh]
    rfl

theorem list_true_eq {G : Graph V} {D : V → Bool} (hD : TotalDominating G D) :
    cardinal G (fun v => D v && support G v) = cardinal G (support G) := by
  apply card_eq
  intro v
  rw [Bool.and_eq_true]
  exact ⟨And.right, fun h => ⟨supports_in_total hD h,h⟩⟩

theorem some_edge_if_not_independent {G : Graph V} (hi : ¬ SupportIndependent G) :
    ∃ a b, support G a = true ∧ support G b = true ∧ Adj G a b := by
  classical
  by_cases he : ∃ a b, support G a = true ∧ support G b = true ∧ Adj G a b
  · exact he
  · exact False.elim (hi (fun a b ha hb h => he ⟨a,b,ha,hb,h⟩))

theorem nonisolates_at_least_two {G : Graph V} (hi : ¬ SupportIndependent G) :
    cardinal G (supportIsolate G) + 2 ≤ cardinal G (support G) := by
  have hs := count_filter_split G.verts (support G) (supportIsolate G)
  have he : cardinal G (fun v => support G v && supportIsolate G v)
           = cardinal G (supportIsolate G) := by
    apply card_eq
    intro v
    rw [Bool.and_eq_true]
    exact ⟨And.right, fun h => ⟨(isolate_char.mp h).1,h⟩⟩
  obtain ⟨a,b,ha,hb,hab⟩ := some_edge_if_not_independent hi
  have ina : a ∈ G.verts.filter (fun v => support G v && !supportIsolate G v) := by
    apply List.mem_filter.mpr
    refine ⟨G.complete a, (Bool.and_eq_true _ _).mpr ⟨ha,?_⟩⟩
    have hni : supportIsolate G a = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      have hf := (isolate_char.mp hh).2
      have hp : 0 < (nbrs G (support G) a).length := member_positive (mem_nbrs.mpr ⟨hab,hb⟩)
      omega
    simp [hni]
  have inb : b ∈ G.verts.filter (fun v => support G v && !supportIsolate G v) := by
    apply List.mem_filter.mpr
    refine ⟨G.complete b, (Bool.and_eq_true _ _).mpr ⟨hb,?_⟩⟩
    have hni : supportIsolate G b = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      have hf := (isolate_char.mp hh).2
      have hp : 0 < (nbrs G (support G) b).length := member_positive (mem_nbrs.mpr ⟨G.symm _ _ hab,ha⟩)
      omega
    simp [hni]
  have htwo := two_members_lower ina inb (adj_ne hab)
  change cardinal G (support G) = cardinal G (fun v => support G v && supportIsolate G v) + _ at hs
  rw [he] at hs
  omega

theorem singleton_support_shape {T : Tree V} {D : V → Bool} {y : V}
    (hD : TotalDominating T.graph D) (hdy : D y=true) (hsy : support T.graph y=false)
    (hdyn : ∀ a, D a=true → support T.graph a=true ∨ a=y)
    (hI : SupportIndependent T.graph) :
    (∀ a, support T.graph a=true → Adj T.graph a y) ∧
    (∀ a, D a=false → ∃ s, support T.graph s=true ∧ Adj T.graph a s ∧ leaf T.graph a=true) := by
  have hstar : ∀ a, support T.graph a=true → Adj T.graph a y := by
    intro a ha
    obtain ⟨w,e,hw⟩ := hD a
    rcases hdyn w hw with hs | he
    · exact False.elim (hI _ _ ha hs e)
    · rwa [he] at e
  have hroute : ∀ a b, D a=true → D b=true →
      ∃ p, TPath T a p b ∧ ∀ z∈a::p, D z=true := by
    intro a b da db
    by_cases e : a=b
    · subst b; exact ⟨[],PathTo.nil,by simpa using da⟩
    rcases hdyn a da with sa | ea <;> rcases hdyn b db with sb | eb
    · have ea : a≠y := by intro h; subst a; simp [hsy] at sa
      have hd : a ∉ [y,b] := by simp [ea,e]
      refine ⟨[y,b],PathTo.cons (hstar a sa) hd (path_single (T.graph.symm _ _ (hstar b sb))),?_⟩
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with ee|ee|ee <;> subst z <;> assumption
    · subst b
      refine ⟨[y],path_single (hstar _ sa),?_⟩
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil,or_false] at hz
      rcases hz with hh|hh <;> subst z <;> assumption
    · subst a
      refine ⟨[b],path_single (T.graph.symm _ _ (hstar _ sb)),?_⟩
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil,or_false] at hz
      rcases hz with hh|hh <;> subst z <;> assumption
    · subst a b; contradiction
  have hattach : ∀ x a b, D x=false → D a=true → D b=true →
      Adj T.graph x a → ∃ p, TPath T x (a::p) b ∧ ∀ z∈a::p, D z=true := by
    intro x a b dx da db exa
    obtain ⟨p,hp,hdom⟩ := hroute a b da db
    have notin : x ∉ a::p := fun hx => by have hh := hdom x hx; simp [dx] at hh
    exact ⟨p,PathTo.cons exa notin hp,hdom⟩
  have hout : ∀ x z, D x=false → D z=false → ¬ Adj T.graph x z := by
    intro x z dx dz exz
    obtain ⟨a,exa,da⟩ := hD x
    obtain ⟨b,ezb,db⟩ := hD z
    obtain ⟨p,hp,hdom⟩ := hattach x a b dx da db exa
    have hd : ∀ t∈x::a::p, t∉[z] := by
      intro t ht ht'
      have he : t=z := by simpa using ht'
      subst t
      rcases List.mem_cons.mp ht with hh|hh
      · exact (adj_ne exz) hh.symm
      · have hpz := hdom z hh
        simp [dz] at hpz
    have hpaths := T.uniquePath _ _ _ _ (path_append hp (path_single (T.graph.symm _ _ ezb)) hd) (path_single exz)
    have hhead : a=z := (List.cons.inj hpaths).1
    subst a
    simp [dz] at da
  refine ⟨hstar,?_⟩
  intro x dx
  obtain ⟨a,exa,da⟩ := hD x
  have huniq : ∀ b, Adj T.graph x b → b=a := by
    intro b exb
    have db : D b=true := by
      cases hh : D b with
      | false => exact False.elim (hout x b dx hh exb)
      | true => rfl
    obtain ⟨p,hp,_⟩ := hattach x a b dx da db exa
    exact ((List.cons.inj (T.uniquePath _ _ _ _ hp (path_single exb))).1).symm
  have hleaf : leaf T.graph x=true := by
    apply leaf_degree.mpr
    have hp : 0 < degree T.graph x := member_positive (mem_nbrs.mpr ⟨exa,rfl⟩)
    have hsmall : degree T.graph x ≤ 1 := by
      apply subset_le_length (filter_nodup T.graph.nodup _) (by simp : [a].Nodup)
      intro b hb
      have hh := huniq b (mem_nbrs.mp hb).1
      simp [hh]
    omega
  rcases hdyn a da with ha | ha
  · exact ⟨a,ha,exa,hleaf⟩
  · subst a
    have hy : support T.graph y=true := decide_eq_true
      (member_positive (mem_nbrs.mpr ⟨T.graph.symm _ _ exa,hleaf⟩))
    simp [hsy] at hy

theorem card_at_most_one {G : Graph V} {P : V → Bool} {u : V}
    (h : ∀ v, P v = true → v=u) : cardinal G P ≤ 1 := by
  apply subset_le_length (filter_nodup G.nodup _) (by simp : [u].Nodup)
  intro v hv
  have h' := h v (List.mem_filter.mp hv).2
  simp [h']

theorem unique_center_of_one_extra {T : Tree V} {D : V → Bool} {y : V}
    (hn : 2 < T.graph.verts.length)
    (hD : TotalDominating T.graph D) (hdy : D y=true) (hsy : support T.graph y=false)
    (hdyn : ∀ a, D a=true → support T.graph a=true ∨ a=y)
    (hI : SupportIndependent T.graph)
    (hS : 0 < cardinal T.graph (support T.graph)) :
    cardinal T.graph (center T) ≤ 1 := by
  obtain ⟨hstar,houtside⟩ := singleton_support_shape hD hdy hsy hdyn hI
  have outsideD (u : V) (hs : support T.graph u=false) (hy : u≠y) : D u=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rcases hdyn u h with h'|h'
    · simp [hs] at h'
    · exact hy h'
  have support_ne_y {u : V} (hs : support T.graph u=true) : u≠y := by
    intro h; subst u; simp [hsy] at hs
  have support_ne_outside {s u : V} (hs : support T.graph s=true)
      (hd : D u=false) : u≠s := by
    intro h; subst u
    have dd := supports_in_total hD hs
    simp [hd] at dd
  by_cases hs1 : cardinal T.graph (support T.graph) ≤ 1
  · obtain ⟨s,hsM⟩ := positive_member hS
    have hs := (List.mem_filter.mp hsM).2
    have seq (u : V) (su : support T.graph u=true) : u=s :=
      singleton_unique hs1 (List.mem_filter.mpr ⟨T.graph.complete _,su⟩) hsM
    have univ : ∀ u, u≠s → Adj T.graph s u := by
      intro u h
      by_cases uy : u=y
      · subst u; exact hstar s hs
      · have hSu : support T.graph u=false := Bool.eq_false_iff.mpr (fun hu => h (seq _ hu))
        obtain ⟨a,ha,hea,_⟩ := houtside u (outsideD u hSu uy)
        rw [seq _ ha] at hea
        exact T.graph.symm _ _ hea
    have eccs : eccentricity T s ≤ 1 := by
      obtain ⟨u,he⟩ := ecc_attains T s
      by_cases hus : u=s
      · subst u
        rw [dist_self] at he
        omega
      · rw [dist_adj (univ u hus)] at he
        omega
    apply card_at_most_one (u:=s)
    intro u hu
    by_cases us : u=s
    · exact us
    · exfalso
      obtain ⟨z,zu,zs⟩ := distinct_third hn us
      have huS : u ∉ [s,z] := by simp [us,Ne.symm zu]
      have p : TPath T u [s,z] z := PathTo.cons
        (T.graph.symm _ _ (univ u us)) huS (path_single (univ z zs))
      have hd := dist_eq p
      have h1 := ecc_upper T u z
      have h2 := center_char.mp hu s
      simp at hd
      omega
  · have ntwo : 2 ≤ cardinal T.graph (support T.graph) := by omega
    obtain ⟨s,hsM,t,htM,hst⟩ := two_members (filter_nodup T.graph.nodup _) ntwo
    have hs := (List.mem_filter.mp hsM).2
    have ht := (List.mem_filter.mp htM).2
    have yNotLeaf : leaf T.graph y=false := by
      apply Bool.eq_false_iff.mpr
      intro hl
      exact hst (leaf_unique_neighbor hl (T.graph.symm _ _ (hstar s hs)) (T.graph.symm _ _ (hstar t ht)))
    have eccy : eccentricity T y ≤ 2 := by
      obtain ⟨u,he⟩ := ecc_attains T y
      by_cases uy : u=y
      · subst u
        rw [dist_self] at he
        omega
      · cases su : support T.graph u with
        | true =>
          rw [dist_adj (T.graph.symm _ _ (hstar u su))] at he
          omega
        | false =>
          obtain ⟨a,ha,hea,_⟩ := houtside u (outsideD u su uy)
          have hyn : y∉[a,u] := by simp [Ne.symm (support_ne_y ha),Ne.symm uy]
          have p : TPath T y [a,u] u := PathTo.cons
            (T.graph.symm _ _ (hstar a ha)) hyn (path_single (T.graph.symm _ _ hea))
          rw [dist_eq p] at he
          simp at he
          omega
    have farLeaf (a : V) : ∃ b p, support T.graph b=true ∧ a≠b ∧
        Adj T.graph b p ∧ leaf T.graph p=true ∧ support T.graph p=false ∧
        p≠y ∧ D p=false := by
      have hb : ∃ b, support T.graph b=true ∧ a≠b := by
        by_cases e : a=s
        · exact ⟨t,ht,e ▸ hst⟩
        · exact ⟨s,hs,e⟩
      obtain ⟨b,hb,hab⟩ := hb
      obtain ⟨p,hbp,hl⟩ := support_has_leaf hb
      have hSp := leaf_not_support (tree_connected T) hn hl
      have hpy : p≠y := by intro h; subst p; simp [yNotLeaf] at hl
      exact ⟨b,p,hb,hab,hbp,hl,hSp,hpy,outsideD p hSp hpy⟩
    apply card_at_most_one (u:=y)
    intro u hu
    by_cases uy : u=y
    · exact uy
    · exfalso
      have hcent := center_char.mp hu y
      cases su : support T.graph u with
      | true =>
        obtain ⟨b,p,hb,hub,hbp,_,hSp,hpy,_⟩ := farLeaf u
        have up : u≠p := by intro h; subst p; simp [su] at hSp
        have hy : y∉[b,p] := by simp [Ne.symm (support_ne_y hb),Ne.symm hpy]
        have huN : u∉[y,b,p] := by simp [uy,hub,up]
        have p2 : TPath T y [b,p] p :=
          PathTo.cons (T.graph.symm _ _ (hstar b hb)) hy (path_single hbp)
        have p3 : TPath T u [y,b,p] p := PathTo.cons (hstar u su) huN p2
        have he := dist_eq p3
        have hEu := ecc_upper T u p
        simp at he
        omega
      | false =>
        have du := outsideD u su uy
        obtain ⟨a,ha,hua,hLu⟩ := houtside u du
        obtain ⟨b,p,hb,hab,hbp,_,hSp,hpy,_⟩ := farLeaf a
        have up : u≠p := by
          intro he
          subst p
          exact hab (leaf_unique_neighbor hLu hua (T.graph.symm _ _ hbp))
        have ap : a≠p := by intro h; subst p; simp [ha] at hSp
        have hyN : y∉[b,p] := by simp [Ne.symm (support_ne_y hb),Ne.symm hpy]
        have haN : a∉[y,b,p] := by simp [support_ne_y ha,hab,ap]
        have huN : u∉[a,y,b,p] := by simp [support_ne_outside ha du,uy,support_ne_outside hb du,up]
        have p2 : TPath T y [b,p] p :=
          PathTo.cons (T.graph.symm _ _ (hstar b hb)) hyN (path_single hbp)
        have p3 : TPath T a [y,b,p] p := PathTo.cons (hstar a ha) haN p2
        have p4 : TPath T u [a,y,b,p] p := PathTo.cons hua huN p3
        have he := dist_eq p4
        have hEu := ecc_upper T u p
        simp at he
        omega

/-- #361 pointwise for every total dominating set of a finite tree. -/
theorem conjecture361 (T : Tree V) (hn : 2 < T.graph.verts.length)
    (D : V → Bool) (hD : TotalDominating T.graph D) :
    cardinal T.graph (supportIsolate T.graph) + cardinal T.graph (center T)
      ≤ cardinal T.graph D := by
  have hcen := centers_at_most_two T
  have hSup := card_mono (G:=T.graph) (P:=support T.graph) (Q:=D)
    (fun _ => supports_in_total hD)
  by_cases hi : SupportIndependent T.graph
  · rw [isolates_all_if_independent hi]
    let O : List V := T.graph.verts.filter (fun v => D v && !support T.graph v)
    have hp := count_filter_split T.graph.verts D (support T.graph)
    change cardinal T.graph D = cardinal T.graph (fun v => D v && support T.graph v) + O.length at hp
    rw [list_true_eq hD] at hp
    by_cases ho : 2 ≤ O.length
    · omega
    · have d2 := total_at_least_two hn hD
      have hs : 0 < cardinal T.graph (support T.graph) := by omega
      obtain ⟨s,hsm⟩ := positive_member hs
      have hss := (List.mem_filter.mp hsm).2
      obtain ⟨y,esy,dy⟩ := hD s
      have sy : support T.graph y = false := Bool.eq_false_iff.mpr (fun sy => hi s y hss sy esy)
      have yM : y∈O := List.mem_filter.mpr ⟨T.graph.complete y,by simp [dy,sy]⟩
      have o1 : O.length = 1 := by have := member_positive yM; omega
      have hdyn : ∀ a, D a=true → support T.graph a=true ∨ a=y := by
        intro a da
        cases sa : support T.graph a with
        | true => exact Or.inl rfl
        | false =>
          have aM : a∈O := List.mem_filter.mpr ⟨T.graph.complete a,by simp [da,sa]⟩
          exact Or.inr (singleton_unique (by omega) aM yM)
      have h1 := unique_center_of_one_extra hn hD dy sy hdyn hi hs
      omega
  · have hnS := nonisolates_at_least_two hi
    omega


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

/-- The literal #361 formula. The tree condition is given by its standard
characterization as a simple graph with exactly one simple path between
each ordered pair of vertices. -/
theorem conjecture361_gamma (T : Tree V) (hn : 2 < T.graph.verts.length) :
    cardinal T.graph (supportIsolate T.graph) + cardinal T.graph (center T)
      ≤ totalDominationNumber T hn := by
  obtain ⟨D,hD,hc⟩ := (Classical.choose_spec (hasMinTotal T hn)).1
  have he : cardinal T.graph D = totalDominationNumber T hn := hc
  rw [← he]
  exact conjecture361 T hn D hD

#print axioms conjecture361_gamma
end Graffiti361
