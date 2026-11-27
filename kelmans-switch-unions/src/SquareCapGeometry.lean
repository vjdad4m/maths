import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.SquareCap
noncomputable section

variable {V : Type*} [Fintype V]

/-- Canonical oriented boundary. -/
def boundary (G : SimpleGraph V) (c : V → Bool) : Finset (V × V) := by
  classical
  exact univ.filter (fun e => c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2)

def flip (c : V → Bool) : V → Bool := fun v => !(c v)

def zone (c d : V → Bool) (i j : Bool) : V → Bool :=
  fun v => (c v == i) && (d v == j)

private theorem flip_card (G : SimpleGraph V) (c : V → Bool) :
    (boundary G (flip c)).card = (boundary G c).card := by
  classical
  unfold boundary
  apply card_bij (fun e _ => e.swap)
  · intro e h
    obtain ⟨hc, hd, ha⟩ := (mem_filter.mp h).2
    exact mem_filter.mpr ⟨mem_univ _, by simpa [flip] using hd, by simpa [flip] using hc, ha.symm⟩
  · intro a _ b _ eq
    exact Prod.swap_injective eq
  · intro e h
    obtain ⟨hc, hd, ha⟩ := (mem_filter.mp h).2
    exact ⟨e.swap, mem_filter.mpr ⟨mem_univ _, by simp [flip,hd],
      by simp [flip,hc], ha.symm⟩, Prod.swap_swap _⟩

private def cost (a b : Bool) : ℕ := if a = true ∧ b = false then 1 else 0

private def edgeCost (G : SimpleGraph V) (c : V → Bool) (e : V × V) : ℕ := by
  classical
  exact if G.Adj e.1 e.2 then cost (c e.1) (c e.2) else 0

private theorem count_sum (G : SimpleGraph V) (c : V → Bool) :
    (boundary G c).card = ∑ e, edgeCost G c e := by
  classical
  rw [show (boundary G c).card = ∑ _e ∈ boundary G c, (1:ℕ) by simp]
  unfold boundary
  rw [sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases adj : G.Adj e.1 e.2 <;> simp [edgeCost,cost,adj]

private theorem table (a b c d : Bool) :
    cost ((a == false) && (b == false)) ((c == false) && (d == false)) +
    cost ((a == false) && (b == true)) ((c == false) && (d == true)) +
    cost ((a == true) && (b == false)) ((c == true) && (d == false)) +
    cost ((a == true) && (b == true)) ((c == true) && (d == true)) ≤
    cost a c + cost (!a) (!c) + cost b d + cost (!b) (!d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Every directed edge leaving an intersection zone also accounts for
at least one directed crossing of a constituent coloring or its flip. -/
theorem zone_cut_sum (G : SimpleGraph V) (c d : V → Bool) :
    (boundary G (zone c d false false)).card + (boundary G (zone c d false true)).card +
    (boundary G (zone c d true false)).card + (boundary G (zone c d true true)).card ≤
    2 * ((boundary G c).card + (boundary G d).card) := by
  have flipc := flip_card G c
  have flipd := flip_card G d
  suffices sum :
      (boundary G (zone c d false false)).card + (boundary G (zone c d false true)).card +
      (boundary G (zone c d true false)).card + (boundary G (zone c d true true)).card ≤
      (boundary G c).card + (boundary G (flip c)).card +
      (boundary G d).card + (boundary G (flip d)).card by omega
  rw [count_sum,count_sum,count_sum,count_sum,count_sum,count_sum,count_sum,count_sum]
  simp only [←sum_add_distrib]
  apply sum_le_sum
  intro e _
  classical
  by_cases adj : G.Adj e.1 e.2
  · simpa only [edgeCost,if_pos adj,zone,flip] using table (c e.1) (d e.1) (c e.2) (d e.2)
  · simp [edgeCost,adj]

/-- If two cuts of size two cross and every intersection zone needs
two edges to leave, all four zones must have exactly two leaving edges. -/
theorem crossing_two_lower_tight (G : SimpleGraph V) (c d : V → Bool)
    (cc : (boundary G c).card ≤ 2) (dc : (boundary G d).card ≤ 2)
    (min : ∀ i j, 2 ≤ (boundary G (zone c d i j)).card) :
    ∀ i j, (boundary G (zone c d i j)).card = 2 := by
  intro i j
  have zz := zone_cut_sum G c d
  have a := min false false
  have b := min false true
  have k := min true false
  have l := min true true
  cases i <;> cases j <;> omega

/-- A crossing two-cut cannot occur when every intersection zone
would be a singleton at a boundary budget of two and the graph
contains more than four vertices. -/
theorem no_crossing_two_rigid_zones (G : SimpleGraph V) (c d : V → Bool)
    (cc : (boundary G c).card ≤ 2) (dc : (boundary G d).card ≤ 2)
    (large : 4 < Fintype.card V)
    (min : ∀ i j, 2 ≤ (boundary G (zone c d i j)).card)
    (rigid : ∀ i j, (boundary G (zone c d i j)).card ≤ 2 →
      ∀ x y, c x = i → d x = j → c y = i → d y = j → x = y) :
    False := by
  have eq := crossing_two_lower_tight G c d cc dc min
  let f : V → Bool × Bool := fun v => (c v,d v)
  have inj : Function.Injective f := by
    intro x y h
    exact rigid (c x) (d x) (eq _ _).le x y rfl rfl
      (congrArg Prod.fst h).symm (congrArg Prod.snd h).symm
  have card := Fintype.card_le_of_injective f inj
  rw [Fintype.card_prod, Fintype.card_bool] at card
  omega

abbrev Port := Bool × Bool

def portCount (p : Port ↪ V) (c : V → Bool) (b : Bool) : ℕ :=
  ((univ : Finset Port).filter (fun i => c (p i) = b)).card

def mismatch (p : Port ↪ V) (c : V → Bool) (t : Port → Bool) : ℕ :=
  ((univ : Finset Port).filter (fun i => c (p i) ≠ t i)).card

def NontrivialSide (c : V → Bool) (b : Bool) : Prop :=
  ∃ x y, c x = b ∧ c y = b ∧ x ≠ y

/-- Deleting a square with distinct external contacts imposes these
on each outside shore by restoring the whole square to the other side. -/
structure OutsideLaw (G : SimpleGraph V) (p : Port ↪ V) : Prop where
  weak : ∀ c b, (∃ x, c x = b) → 3 ≤ (boundary G c).card + portCount p c b
  strong : ∀ c b, NontrivialSide c b → 4 ≤ (boundary G c).card + portCount p c b

omit [Fintype V] in
private theorem portCount_complement (p : Port ↪ V) (c : V → Bool) :
    portCount p c true + portCount p c false = 4 := by
  have d : Disjoint ((univ : Finset Port).filter (fun i => c (p i) = true))
    ((univ : Finset Port).filter (fun i => c (p i) = false)) := by
    simp [disjoint_left]
  have e : ((univ : Finset Port).filter (fun i => c (p i) = true)) ∪
    ((univ : Finset Port).filter (fun i => c (p i) = false)) = univ := by
    ext i
    cases c (p i) <;> simp
  unfold portCount
  rw [←card_union_of_disjoint d,e,card_univ,Fintype.card_prod,Fintype.card_bool]

omit [Fintype V] in
private theorem portCount_le_one (p : Port ↪ V) (c : V → Bool) (b : Bool)
    (ns : ¬ NontrivialSide c b) : portCount p c b ≤ 1 := by
  unfold portCount
  apply card_le_one.mpr
  intro i hi j hj
  by_contra ne
  exact ns ⟨p i,p j,(mem_filter.mp hi).2,(mem_filter.mp hj).2,
    fun eq => ne (p.injective eq)⟩

omit [Fintype V] in
private theorem mismatch_zero (p : Port ↪ V) (c : V → Bool) (t : Port → Bool)
    (h : mismatch p c t = 0) : ∀ i, c (p i) = t i := by
  intro i
  by_contra ne
  have e := card_eq_zero.mp h
  have mem : i ∈ (univ : Finset Port).filter (fun i => c (p i) ≠ t i) :=
    mem_filter.mpr ⟨mem_univ _,ne⟩
  rw [e] at mem
  simp at mem

def coord (k : Bool) (i : Port) : Bool := if k then i.1 else i.2

private theorem coord_fiber_two (k a : Bool) : ∃ i j : Port,i ≠ j ∧ coord k i = a ∧ coord k j = a := by
  revert k a
  decide

/-- Every nontrivial small cut of a mixed (oppositely colored) cap is
a 2-cut of the outside graph with perfect agreement on all ports. -/
theorem split_budget_two {G : SimpleGraph V} {p : Port ↪ V} (L : OutsideLaw G p)
    (c : V → Bool) (k : Bool) (s : Bool → Bool) (sep : s false ≠ s true)
    (nonempty : ∀ b, ∃ x, c x = b)
    (budget : (boundary G c).card + mismatch p c (s ∘ coord k) + 1 ≤ 3) :
    (boundary G c).card = 2 ∧ (∀ i, c (p i) = s (coord k i)) := by
  have full (b : Bool) : NontrivialSide c b := by
    by_contra ns
    have d := L.weak c b (nonempty b)
    have psmall := portCount_le_one p c b ns
    have zero : mismatch p c (s ∘ coord k) = 0 := by omega
    have agree := mismatch_zero p c _ zero
    have surj : ∃ a, s a = b := by
      cases fs : s false <;> cases ts : s true <;> cases b <;> simp_all
    obtain ⟨a,ea⟩ := surj
    obtain ⟨i,j,ij,ki,kj⟩ := coord_fiber_two k a
    exact ns ⟨p i,p j,(agree i).trans (by simp [ki,ea]),
      (agree j).trans (by simp [kj,ea]),fun eq => ij (p.injective eq)⟩
  have law₀ := L.strong c false (full false)
  have law₁ := L.strong c true (full true)
  have sides := portCount_complement p c
  have eq : (boundary G c).card = 2 := by omega
  have zero : mismatch p c (s ∘ coord k) = 0 := by omega
  exact ⟨eq,mismatch_zero p c _ zero⟩

omit [Fintype V] in
private theorem zone_one_port (p : Port ↪ V) (c d : V → Bool) (i j : Bool)
    (cfit : ∀ a, c (p a) = a.1) (dfit : ∀ a, d (p a) = a.2) :
    portCount p (zone c d i j) true = 1 := by
  have eq : (univ : Finset Port).filter (fun a => zone c d i j (p a) = true) = {(i,j)} := by
    ext a
    simp [zone,cfit,dfit,Prod.ext_iff]
  unfold portCount
  rw [eq,card_singleton]

/-- If the outside graph has at least five vertices, only one of the
two coordinate pairings may have a compatible 2-edge split. -/
theorem no_two_bad_coordinate_splits
    {G : SimpleGraph V} {p : Port ↪ V} (L : OutsideLaw G p)
    (large : 4 < Fintype.card V)
    (c d : V → Bool)
    (cb : (boundary G c).card ≤ 2) (db : (boundary G d).card ≤ 2)
    (cfit : ∀ a, c (p a) = a.1) (dfit : ∀ a, d (p a) = a.2) : False := by
  have zcard := zone_one_port p c d
  apply no_crossing_two_rigid_zones G c d cb db large
  · intro i j
    have chosen : zone c d i j (p (i,j)) = true := by simp [zone,cfit,dfit]
    have bound := L.weak (zone c d i j) true ⟨p (i,j),chosen⟩
    rw [zcard i j cfit dfit] at bound
    omega
  · intro i j h x y cx dx cy dy
    by_contra ne
    have bound := L.strong (zone c d i j) true
      ⟨x,y,by simp [zone,cx,dx],by simp [zone,cy,dy],ne⟩
    rw [zcard i j cfit dfit] at bound
    omega

#print axioms split_budget_two
#print axioms no_two_bad_coordinate_splits

variable {T : Type*} [Fintype T]

def attachAdj (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (root : Port → T) : V ⊕ T → V ⊕ T → Prop
  | .inl a,.inl b => G.Adj a b
  | .inr a,.inr b => P.Adj a b
  | .inl a,.inr b => ∃ i, p i = a ∧ root i = b
  | .inr b,.inl a => ∃ i, p i = a ∧ root i = b

omit [Fintype V] [Fintype T] in
def attach (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (root : Port → T) : SimpleGraph (V ⊕ T) where
  Adj := attachAdj G P p root
  symm := by
    intro a b h
    cases a <;> cases b
    · exact G.symm h
    · exact h
    · exact h
    · exact P.symm h
  loopless := by
    intro a
    cases a
    · exact G.loopless _
    · exact P.loopless _

private theorem in_boundary {G : SimpleGraph V} {c : V → Bool} {e : V × V} :
    e ∈ boundary G c ↔ c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2 := by
  classical
  simp [boundary]

omit [Fintype V] [Fintype T] in
private def sideEdge (p : Port ↪ V) (r : Port → T) (c : V → Bool)
    (i : Port) : (V ⊕ T) × (V ⊕ T) :=
  if c (p i) then (Sum.inl (p i),Sum.inr (r i)) else (Sum.inr (r i),Sum.inl (p i))

omit [Fintype V] [Fintype T] in
private theorem inj_sideEdge (p : Port ↪ V) (r : Port → T) (c : V → Bool) :
    Function.Injective (sideEdge p r c) := by
  intro i j h
  unfold sideEdge at h
  split at h <;> split at h <;> simp_all [p.injective.eq_iff]

/-- Exact boundary count: outside, interior gadget, and port wires have
disjoint edge supports; each mismatched wire contributes one edge. -/
theorem attach_boundary (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (r : Port → T) (c : V → Bool) (s : T → Bool) :
    (boundary (attach G P p r) (Sum.elim c s)).card =
      (boundary G c).card + (boundary P s).card + mismatch p c (s ∘ r) := by
  classical
  let i : V ↪ V ⊕ T := ⟨Sum.inl,Sum.inl_injective⟩
  let j : T ↪ V ⊕ T := ⟨Sum.inr,Sum.inr_injective⟩
  let A := (boundary G c).map (i.prodMap i)
  let B := (boundary P s).map (j.prodMap j)
  let X := (univ.filter (fun a : Port => c (p a) ≠ s (r a))).image (sideEdge p r c)
  have XA (u v : V) : (Sum.inl u,Sum.inl v) ∉ X := by
    intro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    unfold sideEdge at eq
    split at eq <;> simp at eq
  have XB (u v : T) : (Sum.inr u,Sum.inr v) ∉ X := by
    intro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    unfold sideEdge at eq
    split at eq <;> simp at eq
  have split :
      boundary (attach G P p r) (Sum.elim c s) = (A ∪ B) ∪ X := by
    ext ⟨u,v⟩
    rw [in_boundary,mem_union,mem_union]
    cases u with
    | inl u => cases v with
      | inl v =>
        simp [A,B, i,j, mem_map, Function.Embedding.prodMap, XA,in_boundary,attach,attachAdj]
      | inr v =>
        have left : (c u = true ∧ s v = false ∧ ∃ i, p i = u ∧ r i = v) ↔
            (Sum.inl u,Sum.inr v) ∈ X := by
          constructor
          · rintro ⟨ht,hf,a,rfl,rfl⟩
            exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,by simp [ht,hf]⟩,by simp [sideEdge,ht]⟩
          · intro h
            obtain ⟨a,hi,eq⟩ := mem_image.mp h
            have ne := (mem_filter.mp hi).2
            unfold sideEdge at eq
            split at eq
            · rename_i ht
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa using eq)
              exact ⟨ht,by cases hs : s (r a) <;> simp_all, a,rfl,rfl⟩
            · simp at eq
        simpa [A,B, i,j, mem_map, Function.Embedding.prodMap,attach,attachAdj] using left
    | inr u => cases v with
      | inl v =>
        have left : (s u = true ∧ c v = false ∧ ∃ i, p i = v ∧ r i = u) ↔
            (Sum.inr u,Sum.inl v) ∈ X := by
          constructor
          · rintro ⟨ht,hf,a,rfl,rfl⟩
            exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,by simp [ht,hf]⟩,by simp [sideEdge,hf]⟩
          · intro h
            obtain ⟨a,hi,eq⟩ := mem_image.mp h
            have ne := (mem_filter.mp hi).2
            unfold sideEdge at eq
            split at eq
            · simp at eq
            · rename_i ht
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa using eq)
              exact ⟨by cases hs : s (r a) <;> simp_all, by simpa using ht,a,rfl,rfl⟩
        simpa [A,B, i,j, mem_map, Function.Embedding.prodMap,attach,attachAdj] using left
      | inr v =>
        simp [A,B, i,j, mem_map, Function.Embedding.prodMap, XB, in_boundary,attach,attachAdj]
  have disj1 : Disjoint A B := by
    rw [disjoint_left]
    intro e ha hb
    obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp ha
    simp [B, i,j, mem_map, Function.Embedding.prodMap] at hb
  have disj2 : Disjoint (A ∪ B) X := by
    rw [disjoint_left]
    intro e h hx
    rcases mem_union.mp h with a|b
    · obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp a
      exact XA _ _ hx
    · obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_map.mp b
      exact XB _ _ hx
  rw [split, card_union_of_disjoint disj2, card_union_of_disjoint disj1]
  simp [A,B,X,card_image_of_injective _ (inj_sideEdge p r c),mismatch,Function.comp_def]

#print axioms attach_boundary

def SmallTrivial {W : Type*} [Fintype W] (G : SimpleGraph W) : Prop :=
  ∀ c : W → Bool, (boundary G c).card ≤ 3 →
    (∀ x y, c x = true → c y = true → x = y) ∨ (∀ x y, c x = false → c y = false → x = y)

def MinThree {W : Type*} [Fintype W] (G : SimpleGraph W) : Prop :=
  ∀ c : W → Bool, (∀ b, ∃ x,c x = b) → 3 ≤ (boundary G c).card

private theorem boundary_const {W : Type*} [Fintype W] (G : SimpleGraph W) (b : Bool) :
    (boundary G (fun _ => b)).card = 0 := by
  classical
  cases b <;> simp [boundary]

omit [Fintype V] [Fintype T] in
private theorem mismatch_const (p : Port ↪ V) (r : Port → T) (c : V → Bool) (b : Bool) :
    mismatch p c ((fun _ => !b) ∘ r) = portCount p c b := by
  unfold mismatch portCount
  congr 1
  ext i
  cases b <;> cases h : c (p i) <;> simp [h]

/-- Restoring a deleted gadget entirely on the opposite shore turns
the outside shore-boundary expression into an actual ambient cut. -/
theorem outside_law_of_attachment {G : SimpleGraph V} {P : SimpleGraph T}
    {p : Port ↪ V} {r : Port → T} (two : 1 < Fintype.card T)
    (small : SmallTrivial (attach G P p r)) (min : MinThree (attach G P p r)) :
    OutsideLaw G p := by
  have eq (c : V → Bool) (b : Bool) :
      (boundary (attach G P p r) (Sum.elim c (fun _ => !b))).card =
        (boundary G c).card + portCount p c b := by
    rw [attach_boundary, boundary_const, Nat.add_zero, mismatch_const p r c b]
  obtain ⟨a,_,z,_,az⟩ := one_lt_card.mp (by simpa using two : 1 < (univ : Finset T).card)
  refine ⟨?_,?_⟩
  · rintro c b ⟨x, hx⟩
    rw [←eq c b]
    apply min
    intro d
    by_cases e : d = b
    · exact ⟨Sum.inl x,hx.trans e.symm⟩
    · exact ⟨Sum.inr a,by cases b <;> cases d <;> simp_all⟩
  · rintro c b ⟨x,y,hx,hy,ne⟩
    rw [←eq c b]
    by_contra h
    have budget : (boundary (attach G P p r) (Sum.elim c (fun _ => !b))).card ≤ 3 := by omega
    have bad := small _ budget
    have ex : (Sum.inl x : V ⊕ T) ≠ Sum.inl y := fun eq => ne (Sum.inl_injective eq)
    have ez : (Sum.inr a : V ⊕ T) ≠ Sum.inr z := fun eq => az (Sum.inr_injective eq)
    cases b
    · rcases bad with first|second
      · exact ez (first _ _ rfl rfl)
      · exact ex (second _ _ hx hy)
    · rcases bad with first|second
      · exact ex (first _ _ hx hy)
      · exact ez (second _ _ rfl rfl)

def cap (G : SimpleGraph V) (p : Port ↪ V) (k : Bool) : SimpleGraph (V ⊕ Bool) :=
  attach G ⊤ p (coord k)

private theorem top_bool_boundary (s : Bool → Bool) :
    (boundary (⊤ : SimpleGraph Bool) s).card = if s false = s true then 0 else 1 := by
  rw [count_sum]
  have univ4 : (univ : Finset (Bool × Bool)) =
    {(false,false),(false,true),(true,false),(true,true)} := by decide
  rw [univ4]
  cases h : s false <;> cases h' : s true <;>
    simp [edgeCost,cost,h,h',sum_insert]

omit [Fintype V] in
private theorem normalize_fit (s : Bool → Bool) (sep : s false ≠ s true) :
    ∃ t : Bool → Bool, (t = id ∨ t = Bool.not) ∧ (∀ i,t (s i) = i) := by
  cases h : s false <;> cases h' : s true
  · exact (sep (h.trans h'.symm)).elim
  · exact ⟨id,Or.inl rfl, by intro i; cases i <;> simp [h,h']⟩
  · exact ⟨Bool.not,Or.inr rfl, by intro i; cases i <;> simp [h,h']⟩
  · exact (sep (h.trans h'.symm)).elim

/-- A bad cap determines an outside 2-cut realizing the designated
pairing. Both monochrome gadgets and unmixed outside colorings are
handled without any assumption about nontrivial cut sizes in the cap. -/
theorem bad_cap_forces_two_split {G : SimpleGraph V} {p : Port ↪ V} (L : OutsideLaw G p)
    (k : Bool) (bad : ¬ SmallTrivial (cap G p k)) :
    ∃ c, (boundary G c).card ≤ 2 ∧ ∀ i, c (p i) = coord k i := by
  unfold SmallTrivial at bad
  push_neg at bad
  obtain ⟨f,budget,falseSmall,trueSmall⟩ := bad
  let c : V→Bool := f ∘ Sum.inl
  let s : Bool→Bool := f ∘ Sum.inr
  have elim : f = Sum.elim c s := by funext v; cases v <;> rfl
  have cb : (boundary G c).card + (boundary (⊤ : SimpleGraph Bool) s).card +
      mismatch p c (s ∘ coord k) ≤ 3 := by
    rwa [elim,cap,attach_boundary] at budget
  have big (b : Bool) : NontrivialSide f b := by
    cases b
    · obtain ⟨x,y,hx,hy,ne⟩ := trueSmall
      exact ⟨x,y,hx,hy,ne⟩
    · obtain ⟨x,y,hx,hy,ne⟩ := falseSmall
      exact ⟨x,y,hx,hy,ne⟩
  have sep : s false ≠ s true := by
    intro eq
    let b := !(s false)
    have idS : s = fun _ => !b := by
      funext i
      cases i <;> simp [b,←eq]
    obtain ⟨x,y,hx,hy,ne⟩ := big b
    have pin (z : V ⊕ Bool) (h : f z = b) : ∃ w : V, z = Sum.inl w ∧ c w = b := by
      cases z with
      | inl w => exact ⟨w,rfl,h⟩
      | inr w =>
        have imp : s w = b := h
        rw [idS] at imp
        exact (by cases b <;> simp at imp : False).elim
    obtain ⟨u,eu,hu⟩ := pin x hx
    obtain ⟨v,ev,hv⟩ := pin y hy
    have room := L.strong c b ⟨u,v,hu,hv,fun e => ne (eu.trans (e ▸ ev.symm))⟩
    rw [idS,boundary_const,mismatch_const p (coord k) c b] at cb
    omega
  have nonempty (b : Bool) : ∃ x,c x = b := by
    by_contra none
    obtain ⟨x,y,hx,hy,ne⟩ := big b
    cases x with
    | inl u => exact none ⟨u,hx⟩
    | inr i =>
      cases y with
      | inl u => exact none ⟨u,hy⟩
      | inr j =>
        change s i = b at hx
        change s j = b at hy
        cases i <;> cases j <;> simp_all
  rw [top_bool_boundary,if_neg sep] at cb
  have bnd : (boundary G c).card + mismatch p c (s ∘ coord k) + 1 ≤ 3 := by omega
  obtain ⟨two,fit⟩ := split_budget_two L c k s sep nonempty bnd
  obtain ⟨t,ident,ts⟩ := normalize_fit s sep
  refine ⟨t ∘ c,?_,?_⟩
  · rcases ident with rfl|rfl
    · exact two.le
    · exact (flip_card G c).trans two |>.le
  · intro i
    exact (congrArg t (fit i)).trans (ts _)

/-- At least one pairing of a four-port cell into a new adjacent pair
preserves the cubic cyclic-four small-cut property, provided the
outside laws hold and more than four vertices remain. -/
theorem exists_good_coordinate_cap {G : SimpleGraph V} {p : Port ↪ V}
    (L : OutsideLaw G p) (large : 4 < Fintype.card V) :
    ∃ k, SmallTrivial (cap G p k) := by
  by_contra h
  push_neg at h
  obtain ⟨c,cb,cf⟩ := bad_cap_forces_two_split L true (h true)
  obtain ⟨d,db,df⟩ := bad_cap_forces_two_split L false (h false)
  exact no_two_bad_coordinate_splits L large c d cb db cf df

#print axioms outside_law_of_attachment
#print axioms bad_cap_forces_two_split
#print axioms exists_good_coordinate_cap

omit [Fintype V] [Fintype T] in
private def leftNeighborMap (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (r : Port → T) (x : V) :
    G.neighborSet x ⊕ {i : Port // p i = x} →
      (attach G P p r).neighborSet (Sum.inl x)
  | .inl v => ⟨Sum.inl v.val,v.property⟩
  | .inr i => ⟨Sum.inr (r i.val),⟨i.val,i.property,rfl⟩⟩

omit [Fintype V] [Fintype T] in
private theorem leftNeighbor_bij (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (r : Port → T) (x : V) :
    Function.Bijective (leftNeighborMap G P p r x) := by
  constructor
  · intro a b eq
    have h := congrArg Subtype.val eq
    cases a with
    | inl u => cases b with
      | inl v =>
        exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective h))
      | inr i => simp [leftNeighborMap] at h
    | inr i => cases b with
      | inl v => simp [leftNeighborMap] at h
      | inr j =>
        exact congrArg Sum.inr (Subtype.ext (p.injective (i.property.trans j.property.symm)))
  · rintro ⟨a,h⟩
    cases a with
    | inl u => exact ⟨Sum.inl ⟨u,h⟩,rfl⟩
    | inr t =>
      obtain ⟨i,pv,rt⟩ : ∃ i, p i = x ∧ r i = t := h
      refine ⟨Sum.inr ⟨i,pv⟩,Subtype.ext ?_⟩
      exact congrArg Sum.inr rt

omit [Fintype V] [Fintype T] in
private def rightNeighborMap (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (r : Port → T) (x : T) :
    {i : Port // r i = x} ⊕ P.neighborSet x →
      (attach G P p r).neighborSet (Sum.inr x)
  | .inl i => ⟨Sum.inl (p i.val),⟨i.val,rfl,i.property⟩⟩
  | .inr v => ⟨Sum.inr v.val,v.property⟩

omit [Fintype V] [Fintype T] in
private theorem rightNeighbor_bij (G : SimpleGraph V) (P : SimpleGraph T) (p : Port ↪ V)
    (r : Port → T) (x : T) :
    Function.Bijective (rightNeighborMap G P p r x) := by
  constructor
  · intro a b eq
    have h := congrArg Subtype.val eq
    cases a with
    | inl u => cases b with
      | inl v => exact congrArg Sum.inl (Subtype.ext (p.injective (Sum.inl_injective h)))
      | inr i => simp [rightNeighborMap] at h
    | inr i => cases b with
      | inl v => simp [rightNeighborMap] at h
      | inr j => exact congrArg Sum.inr (Subtype.ext (Sum.inr_injective h))
  · rintro ⟨a,h⟩
    cases a with
    | inl u =>
      obtain ⟨i,pv,rt⟩ : ∃ i, p i = u ∧ r i = x := h
      refine ⟨Sum.inl ⟨i,rt⟩,Subtype.ext ?_⟩
      exact congrArg Sum.inl pv
    | inr t => exact ⟨Sum.inr ⟨t,h⟩,rfl⟩

/-- An exterior vertex retains one edge per incident port independent
of the chosen gadget. -/
theorem attach_degree_outside [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : SimpleGraph T) (p : Port ↪ V) (r : Port → T)
    [DecidableRel (attach G P p r).Adj] (x : V) :
    (attach G P p r).degree (Sum.inl x) =
      G.degree x + ((univ : Finset Port).filter (fun i => p i = x)).card := by
  classical
  rw [←SimpleGraph.card_neighborSet_eq_degree]
  rw [←Fintype.card_congr (Equiv.ofBijective _ (leftNeighbor_bij G P p r x))]
  rw [Fintype.card_sum,SimpleGraph.card_neighborSet_eq_degree,Fintype.card_subtype]

/-- An interior vertex receives exactly one distinct neighbor for each
port assigned to it. -/
theorem attach_degree_inside [DecidableEq T] (G : SimpleGraph V) (P : SimpleGraph T) [DecidableRel P.Adj]
    (p : Port ↪ V) (r : Port → T) [DecidableRel (attach G P p r).Adj] (x : T) :
    (attach G P p r).degree (Sum.inr x) =
      ((univ : Finset Port).filter (fun i => r i = x)).card + P.degree x := by
  classical
  rw [←SimpleGraph.card_neighborSet_eq_degree]
  rw [←Fintype.card_congr (Equiv.ofBijective _ (rightNeighbor_bij G P p r x))]
  rw [Fintype.card_sum,SimpleGraph.card_neighborSet_eq_degree,Fintype.card_subtype]

private theorem coord_degree (k x : Bool) :
    ((univ : Finset Port).filter (fun i => coord k i = x)).card = 2 := by
  revert k x
  decide

private theorem top_bool_degree (x : Bool) :
    (⊤ : SimpleGraph Bool).degree x = 1 := by
  revert x
  decide

/-- The square-cap replacement preserves cubicity. Only the outside
degree assumptions from the original gadget are used. -/
theorem cap_cubic [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {P : SimpleGraph T}
    {p : Port ↪ V} {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (cub : ∀ x,(attach G P p r).degree (Sum.inl x) = 3)
    (k : Bool) [DecidableRel (cap G p k).Adj] :
    ∀ x,(cap G p k).degree x = 3 := by
  intro x
  cases x with
  | inl x =>
    unfold cap
    rw [attach_degree_outside]
    have h := cub x
    rw [attach_degree_outside] at h
    exact h
  | inr x =>
    unfold cap
    rw [attach_degree_inside,coord_degree,top_bool_degree]

#print axioms attach_degree_outside
#print axioms attach_degree_inside
#print axioms cap_cubic

private theorem singleton_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→Bool) (x : V) (hx : c x=true)
    (uniq : ∀ y,c y=true→y=x) :
    (boundary G c).card = G.degree x := by
  classical
  let f : V → V × V := fun v => (x,v)
  have equal : boundary G c = (G.neighborFinset x).image f := by
    ext z
    obtain ⟨u,v⟩ := z
    constructor
    · intro h
      obtain ⟨hu,_,huv⟩ := in_boundary.mp h
      have e := uniq u hu
      refine mem_image.mpr ⟨v,(mem_neighborFinset G x v).mpr (e ▸ huv),?_⟩
      exact Prod.ext e.symm rfl
    · intro h
      obtain ⟨w,hw,eq⟩ := mem_image.mp h
      have eq' : (x,w) = (u,v) := eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq'
      have a := (mem_neighborFinset G x w).mp hw
      have no : c w = false := by
        by_contra! e
        have t : c w = true := by cases h : c w <;> simp_all
        have v_eq := uniq w t
        exact a.ne v_eq.symm
      exact in_boundary.mpr ⟨hx,no,a⟩
  rw [equal,card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),
    card_neighborFinset_eq_degree]

/-- The small-cut property plus cubicity give the ordinary lower
bound of three on every proper cut, including singleton cuts. -/
theorem min_three_of_small_trivial [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (cub : ∀ v,G.degree v = 3)
    (small : SmallTrivial G) : MinThree G := by
  intro c nonempty
  by_contra! few
  rcases small c (by omega) with one|zero
  · obtain ⟨x,hx⟩ := nonempty true
    have eq := singleton_boundary G c x hx (fun y hy => one y x hy hx)
    have d := cub x
    omega
  · obtain ⟨x,hx⟩ := nonempty false
    have eq := singleton_boundary G (flip c) x (by simp [flip,hx]) (fun y hy =>
      zero y x (by simpa [flip] using hy) hx)
    have card := flip_card G c
    have d := cub x
    omega

/-- The complete geometric replacement theorem. The two new vertices
are adjacent by construction. The old gadget can be any size ≥2;
the square application specializes it to exactly four vertices. -/
theorem cubic_good_cap [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph T} {p : Port ↪ V} {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (two : 1 < Fintype.card T) (large : 4 < Fintype.card V)
    (cub : ∀ x,(attach G P p r).degree x = 3)
    (small : SmallTrivial (attach G P p r)) :
    ∃ k, SmallTrivial (cap G p k) ∧ (∀ x, @SimpleGraph.degree _ (cap G p k) x
      (Fintype.ofFinite _)=3) := by
  classical
  have min := min_three_of_small_trivial cub small
  have L := outside_law_of_attachment two small min
  obtain ⟨k,h⟩ := exists_good_coordinate_cap L large
  refine ⟨k,h,?_⟩
  intro x
  rw [Subsingleton.elim (Fintype.ofFinite _) (show Fintype ((cap G p k).neighborSet x) from inferInstance)]
  exact cap_cubic (fun v => cub (Sum.inl v)) k x

#print axioms min_three_of_small_trivial
#print axioms cubic_good_cap

section ThreeConnectivity
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- This is the exact KelmansStarter deletion formulation. -/
def ThreeConnected (G : SimpleGraph W) : Prop :=
  4 ≤ Fintype.card W ∧
    ∀ S : Finset W, S.card ≤ 2 → (G.induce {v : W | v ∉ S}).Connected

variable (G : SimpleGraph W)
variable [DecidableRel G.Adj]

private abbrev survivors (D : Finset W) : Set W := {x | x∉D}

private def component_colour {D : Finset W} (x : survivors D) (v : W) : Bool := by
  classical
  exact if h : v∉D then decide ((G.induce (survivors D)).Reachable x ⟨v,h⟩) else false

omit [Fintype W] [DecidableRel G.Adj] in
private theorem component_colour_true_iff {D : Finset W}
    (x : survivors D) (v : W) :
    component_colour G x v=true ↔ ∃ h : v∉D,(G.induce (survivors D)).Reachable x ⟨v,h⟩ := by
  classical
  by_cases h : v∉D
  · simp [component_colour,h]
  · simp [component_colour,h]

omit [Fintype W] [DecidableRel G.Adj] in
private theorem reach_colour {D : Finset W} (x v : survivors D) :
    component_colour G x v.val=true ↔ (G.induce (survivors D)).Reachable x v := by
  rw [component_colour_true_iff]
  exact ⟨fun ⟨_,r⟩=>r,fun r=>⟨v.property,r⟩⟩

omit [DecidableEq W] in
private theorem survivor_neighbor (cub : ∀v,G.degree v=3) {D : Finset W} (small : D.card≤2)
    (x : survivors D) : ∃ y : survivors D, (G.induce (survivors D)).Adj x y := by
  classical
  by_contra! no
  have sub : G.neighborFinset x.val ⊆ D := by
    intro v mv
    by_contra! h
    exact no ⟨v,h⟩ ((mem_neighborFinset G x.val v).mp mv)
  have b := card_le_card sub
  rw [card_neighborFinset_eq_degree,cub] at b
  omega

private theorem component_cut_big (cub : ∀v,G.degree v=3) (smallCut : SmallTrivial G)
    {D : Finset W} (small : D.card≤2) {x y : survivors D}
    (separate : ¬(G.induce (survivors D)).Reachable x y) :
    4≤(boundary G (component_colour G x)).card := by
  classical
  obtain ⟨u,ed1⟩ := survivor_neighbor G cub small x
  obtain ⟨v,ed2⟩ := survivor_neighbor G cub small y
  have cxx : component_colour G x x.val=true := (reach_colour G x x).mpr (Reachable.refl _)
  have cxy : component_colour G x y.val=false := by
    by_contra! h
    exact separate ((reach_colour G x y).mp (by simpa using h))
  have cxu : component_colour G x u.val=true := (reach_colour G x u).mpr ed1.reachable
  have cxv : component_colour G x v.val=false := by
    by_contra! h
    exact separate (((reach_colour G x v).mp (by simpa using h)).trans ed2.reachable.symm)
  by_contra! tiny
  rcases smallCut (component_colour G x) (by omega) with one|other
  · exact (show G.Adj x.val u.val from ed1).ne (one _ _ cxx cxu)
  · exact (show G.Adj y.val v.val from ed2).ne (other _ _ cxy cxv)

private def incoming (D : Finset W) : Finset (W×W) :=
  D.biUnion (fun v=>(G.neighborFinset v).image (fun w=>(w,v)))

private theorem incoming_card_le (cub : ∀v,G.degree v=3) (D : Finset W) :
    (incoming G D).card≤3*D.card := by
  classical
  unfold incoming
  apply (card_biUnion_le).trans
  have c (v : W) : ((G.neighborFinset v).image (fun w=>(w,v))).card≤3 := by
    apply card_image_le.trans
    rw [card_neighborFinset_eq_degree,cub]
  calc
    (∑ v∈D,((G.neighborFinset v).image (fun w=>(w,v))).card) ≤ ∑ _∈D,3 :=
      sum_le_sum (fun v _=>c v)
    _ = _ := by simp [Nat.mul_comm]

private theorem component_incoming {D : Finset W} (x : survivors D) :
    boundary G (component_colour G x) ⊆ incoming G D := by
  rintro ⟨u,v⟩ h
  obtain ⟨yes,no,e⟩ := in_boundary.mp h
  obtain ⟨hu,ru⟩ := (component_colour_true_iff G x u).mp yes
  have inD : v∈D := by
    by_contra nd
    have edge : (G.induce (survivors D)).Adj ⟨u,hu⟩ ⟨v,nd⟩ := e
    have y := (component_colour_true_iff G x v).mpr ⟨nd,ru.trans edge.reachable⟩
    rw [no] at y
    contradiction
  exact mem_biUnion.mpr ⟨v,inD,mem_image.mpr
    ⟨u,(mem_neighborFinset G v u).mpr e.symm,rfl⟩⟩

/-- Absence of nontrivial cuts of size at most three implies
3-vertex-connectivity in a simple cubic graph. After deleting at
most two vertices, two different components would each have
at least four edges going into the deletion set of capacity six. -/
theorem three_connected_of_small_trivial (cub : ∀v,G.degree v=3)
    (large : 4≤Fintype.card W) (smallCut : SmallTrivial G) :
    ThreeConnected G := by
  classical
  refine ⟨large,?_⟩
  intro D small
  haveI : Nonempty (survivors D) := by
    have lt : D.card<(univ:Finset W).card := by rw [card_univ]; omega
    obtain ⟨v,_,h⟩ := exists_mem_not_mem_of_card_lt_card lt
    exact ⟨⟨v,h⟩⟩
  constructor
  intro x y
  by_contra separate
  let R := G.induce (survivors D)
  let F := boundary G (component_colour G x)
  let H := boundary G (component_colour G y)
  have lx : 4≤F.card := component_cut_big G cub smallCut small separate
  have ly : 4≤H.card := component_cut_big G cub smallCut small (fun r=>separate r.symm)
  have dj : Disjoint F H := by
    apply disjoint_left.mpr
    intro z zF zH
    obtain ⟨e,ex⟩ := (component_colour_true_iff G x z.1).mp (in_boundary.mp zF).1
    obtain ⟨f,ey⟩ := (component_colour_true_iff G y z.1).mp (in_boundary.mp zH).1
    exact separate (ex.trans ey.symm)
  have sub : F∪H⊆incoming G D := union_subset (component_incoming G x) (component_incoming G y)
  have lc := card_le_card sub
  rw [card_union_of_disjoint dj] at lc
  have capacity := incoming_card_le G cub D
  omega


#print axioms three_connected_of_small_trivial
end ThreeConnectivity

#print axioms zone_cut_sum
#print axioms crossing_two_lower_tight
#print axioms no_crossing_two_rigid_zones

end
end KelmansCactus.AtomicBridge.SquareCap
