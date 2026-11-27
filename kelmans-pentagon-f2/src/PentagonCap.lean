import PentagonProfile

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PentagonCap
open SquareCap (boundary SmallTrivial MinThree NontrivialSide min_three_of_small_trivial)
open PentagonProfile
noncomputable section
variable {V : Type*} [Fintype V]

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

def path3 : SimpleGraph (Fin 3) where
  Adj x y := x.val + 1 = y.val ∨ y.val + 1 = x.val
  symm := by
    intro a b h
    exact h.elim Or.inr Or.inl
  loopless := by intro x h; omega

instance : DecidableRel path3.Adj := fun x y =>
  inferInstanceAs (Decidable (x.val+1=y.val ∨ y.val+1=x.val))

def pathRoot (i : Port) : Fin 3 := if i = 1 ∨ i = 4 then 2 else if i = 0 then 1 else 0

def pathCap (G : SimpleGraph V) (p : Port ↪ V) := attach G path3 p pathRoot

private def pc (s : Fin 3 → Bool) : ℕ :=
  ((univ : Finset (Fin 3 × Fin 3)).filter
    (fun z => s z.1=true ∧ s z.2=false ∧ path3.Adj z.1 z.2)).card

private theorem pc_eq (s : Fin 3 → Bool) : (boundary path3 s).card=pc s := by
  classical
  unfold boundary pc
  congr 1
  ext z
  simp

private theorem path_colour_table (s : Fin 3 → Bool) :
    (∃ b, (∀ i,s i = b) ∧ pc s = 0) ∨
    ∃ t b, (∀ i,s i=b ↔ i=t) ∧
      (t=1 ∧ pc s=2 ∧ portWeight (s ∘ pathRoot) b=1 ∨
       t≠1 ∧ pc s=1 ∧ (∀ z,2≤portWeight (s ∘ pathRoot) z)) := by
  revert s
  decide

private theorem nontriv_of_sum_elim {V T : Type*} (c : V→Bool) (s : T→Bool) (b : Bool)
    (big : NontrivialSide (Sum.elim c s) b) (none : ∀ t,s t ≠ b) :
    NontrivialSide c b := by
  obtain ⟨x,y,hx,hy,xy⟩ := big
  cases x with
  | inr x => exact (none x hx).elim
  | inl x => cases y with
    | inr y => exact (none y hy).elim
    | inl y => exact ⟨x,y,hx,hy,fun e=>xy (congrArg Sum.inl e)⟩

omit [Fintype V] in
private theorem same_exterior_mismatch (p : Port ↪ V) (c : V→Bool) (t : Port→Bool)
    (b : Bool) (all : ∀ x,c x ≠ b) :
    mismatch p c t = portWeight t b := by
  unfold portWeight mismatch
  congr 1
  ext i
  have nd := all (p i)
  cases h : c (p i) <;> cases t i <;> cases b <;> simp_all

/-- A failure of the proposed concrete pentagon cap must exactly
separate one of its two configured leaf-port pairs, and nothing
else. The two outside sides each have at least two vertices. -/
theorem bad_path_cap_profile {G : SimpleGraph V} {p : Port ↪ V} (L : OutsideLaw G p)
    (fail : ¬ SmallTrivial (pathCap G p)) :
    ∃ c : V→Bool, ∃ t : Fin 3, ∃ b : Bool,
      t≠1 ∧ (boundary G c).card=2 ∧ (∀ i,c (p i)=b ↔ pathRoot i=t) ∧
        ∀ q,NontrivialSide c q := by
  unfold SmallTrivial at fail
  push_neg at fail
  obtain ⟨f,budget,trueSize,falseSize⟩ := fail
  let c : V→Bool := f ∘ Sum.inl
  let s : Fin 3→Bool := f ∘ Sum.inr
  have eb : f = Sum.elim c s := by funext x; cases x <;> rfl
  have big (b : Bool) : NontrivialSide (Sum.elim c s) b := by
    rw [←eb]
    cases b
    · obtain ⟨x,y,hx,hy,ne⟩ := falseSize
      exact ⟨x,y,hx,hy,ne⟩
    · obtain ⟨x,y,hx,hy,ne⟩ := trueSize
      exact ⟨x,y,hx,hy,ne⟩
  have capBudget : (boundary G c).card + mismatch p c (s ∘ pathRoot) + pc s ≤ 3 := by
    rw [eb,pathCap,attach_boundary,pc_eq] at budget
    omega
  rcases path_colour_table s with ⟨b,all,cut⟩ | ⟨t,b,single,profile⟩
  · have sEq : s = fun _ => !(!b) := by funext x; simp [all]
    have d := L.strong c (!b) (nontriv_of_sum_elim c s (!b) (big (!b))
      (fun x => by simp [all]))
    have mis : mismatch p c (s ∘ pathRoot)=portCount p c (!b) := by
      rw [sEq]
      apply mismatch_const
    omega
  have outside_mixed (z : Bool) : ∃ x,c x=z := by
    by_contra! none
    have sv : z ≠ b := by
      rintro rfl
      obtain ⟨x,y,hx,hy,ne⟩ := big z
      cases x with
      | inl x => exact none x hx
      | inr x => cases y with
        | inl y => exact none y hy
        | inr y => exact ne (congrArg Sum.inr
            ((single x).mp hx |>.trans ((single y).mp hy).symm))
    have mis := same_exterior_mismatch p c (s ∘ pathRoot) z none
    rcases profile with ⟨_,ed,min⟩ | ⟨_,ed,slots⟩
    · have all := portCount_complement (Function.Embedding.refl Port) (s ∘ pathRoot)
      change portWeight (s ∘ pathRoot) true + portWeight (s ∘ pathRoot) false=5 at all
      cases z <;> cases b
      all_goals simp_all
      all_goals omega
    · have pm := slots z
      have pn := slots b
      have all := portCount_complement (Function.Embedding.refl Port) (s ∘ pathRoot)
      change portWeight (s ∘ pathRoot) true + portWeight (s ∘ pathRoot) false=5 at all
      -- The singleton gadget leaf has exactly two ports. Its opposite
      -- color has three, so if z is absent outside the cap budget fails.
      have two : portWeight (s ∘ pathRoot) b=2 := by
        have test : ∀ (s : Fin 3→Bool) (t : Fin 3) (b : Bool),
            t≠1 → (∀ i,s i=b ↔ i=t) → portWeight (s ∘ pathRoot) b=2 := by decide
        exact test _ _ _ (by assumption) single
      cases z <;> cases b
      all_goals simp_all
      all_goals omega
  rcases profile with ⟨_,ct,slots⟩ | ⟨leaf,ct,slots⟩
  · exact (middle_split_impossible L c _ b slots outside_mixed (by omega)).elim
  · obtain ⟨two,agree,big⟩ :=
      leaf_split_is_exact_two L c (s ∘ pathRoot) slots outside_mixed (by omega)
    exact ⟨c,t,b,leaf,two,fun i => (agree i) ▸ single (pathRoot i),big⟩

/-- Assign ports 1,4 to the retained leaf, ports 2,3 to the
discarded leaf and port 0 to the discarded center. -/
theorem good_path_cap_of_no_leaf_split {G : SimpleGraph V} {p : Port ↪ V}
    (L : OutsideLaw G p)
    (no : ∀ (c : V→Bool) (t : Fin 3) (b : Bool), t≠1 →
      (boundary G c).card=2 → (∀ i,c (p i)=b ↔ pathRoot i=t) → False) :
    SmallTrivial (pathCap G p) := by
  by_contra fail
  obtain ⟨c,t,b,leaf,two,fit,_⟩ := bad_path_cap_profile L fail
  exact no c t b leaf two fit

private theorem path_cap_interior_degree (x : Fin 3) :
    ((univ : Finset Port).filter (fun i=>pathRoot i=x)).card + path3.degree x = 3 := by
  revert x
  decide

theorem path_cap_cubic [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph T} {p : Port ↪ V} {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (cub : ∀ x,(attach G P p r).degree (Sum.inl x)=3)
    [DecidableRel (pathCap G p).Adj] :
    ∀ x,(pathCap G p).degree x=3 := by
  intro x
  cases x with
  | inl x =>
    unfold pathCap
    rw [attach_degree_outside]
    have h := cub x
    rw [attach_degree_outside] at h
    exact h
  | inr x =>
    unfold pathCap
    rw [attach_degree_inside]
    exact path_cap_interior_degree x

/-- In a cubic graph this is the cut formulation for having no
cycle-separating edge cut of size ≤4. Keeping it explicit distinguishes
it from the invalid stronger predicate excluding even a 2-vertex shore. -/
def SmallFourTrivial {W : Type*} [Fintype W] (G : SimpleGraph W) : Prop :=
  ∀ c : W→Bool, (boundary G c).card≤4 → ∃ b : Bool,
    ∀ x y z, c x=b → c y=b → c z=b → x=y ∨ x=z ∨ y=z

omit [Fintype V] in
private theorem fiber_one [DecidableEq V] (p : Port ↪ V) (i : Port) :
    ((univ : Finset Port).filter (fun j => p j = p i)).card=1 := by
  have same : (univ : Finset Port).filter (fun j => p j = p i) = {i} := by
    ext j
    simp [p.injective.eq_iff]
  rw [same,card_singleton]

private theorem orient_big_cut [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : V→Bool) (b : Bool) {u v : V}
    (uv : u ≠ v) (cu : c u=b) (cv : c v=b)
    (only : ∀ x,c x=b → x=u ∨ x=v)
    (du : G.degree u=2) (dv : G.degree v=2)
    (ee : ¬G.Adj u v) :
    4 ≤ (boundary G c).card := by
  classical
  let endpoint (a w : V) := if b then (a,w) else (w,a)
  let A := (G.neighborFinset u).image (endpoint u)
  let B := (G.neighborFinset v).image (endpoint v)
  have occupy (a w : V) (h : G.Adj a w) (ax : c a=b) (wx : c w≠b) :
      endpoint a w ∈ boundary G c := by
    cases b
    · have wt : c w=true := by cases h : c w <;> simp_all
      exact in_boundary.mpr ⟨wt,ax,h.symm⟩
    · have wf : c w=false := by cases h : c w <;> simp_all
      exact in_boundary.mpr ⟨ax,wf,h⟩
  have intoA : A ⊆ boundary G c := by
    intro t ht
    obtain ⟨w,wn,rfl⟩ := mem_image.mp ht
    have ed := (mem_neighborFinset G u w).mp wn
    exact occupy u w ed cu (fun h => (only w h).elim
      (fun e => ed.ne e.symm) (fun e => ee (e ▸ ed)))
  have intoB : B ⊆ boundary G c := by
    intro t ht
    obtain ⟨w,wn,rfl⟩ := mem_image.mp ht
    have ed := (mem_neighborFinset G v w).mp wn
    exact occupy v w ed cv (fun h => (only w h).elim
      (fun e => ee (e ▸ ed).symm) (fun e => ed.ne e.symm))
  have dj : Disjoint A B := by
    apply disjoint_left.mpr
    intro t a b'
    obtain ⟨x,_,e⟩ := mem_image.mp a
    obtain ⟨y,_,f⟩ := mem_image.mp b'
    have clash := e.trans f.symm
    cases h : b
    · exact uv (by simpa [endpoint,h] using congrArg Prod.snd clash)
    · exact uv (by simpa [endpoint,h] using congrArg Prod.fst clash)
  have inj (a : V) : Function.Injective (endpoint a) := by
    intro x y e
    cases h : b
    · simpa [endpoint,h] using congrArg Prod.fst e
    · simpa [endpoint,h] using congrArg Prod.snd e
  have eqA : A.card=2 := by rw [card_image_of_injective _ (inj u),card_neighborFinset_eq_degree,du]
  have eqB : B.card=2 := by rw [card_image_of_injective _ (inj v),card_neighborFinset_eq_degree,dv]
  have lower := card_le_card (union_subset intoA intoB)
  rw [card_union_of_disjoint dj,eqA,eqB] at lower
  exact lower

/-- If the ambient is cyclically five-edge-connected in the explicit
cut sense, the only profile capable of breaking a leaf pair is an
edge between its two exterior endpoints. -/
theorem cyclic5_bad_pair_requires_edge [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : SimpleGraph (Fin 5)} {p : Port ↪ V}
    {r : Port → Fin 5} [DecidableRel (attach G P p r).Adj]
    (strong : SmallFourTrivial (attach G P p r))
    (cub : ∀ x,(attach G P p r).degree (Sum.inl x)=3)
    (c : V→Bool) (b : Bool) {i j : Port} (ij : i ≠ j)
    (two : (boundary G c).card=2)
    (fit : ∀ a,c (p a)=b ↔ a=i ∨ a=j) : G.Adj (p i) (p j) := by
  classical
  have uu := (fit i).mpr (Or.inl rfl)
  have vv := (fit j).mpr (Or.inr rfl)
  have uv : p i ≠ p j := fun h=>ij (p.injective h)
  have pn : portCount p c b=2 := by
    have eq : (univ : Finset Port).filter (fun a => c (p a)=b) = {i,j} := by
      ext a
      simp [fit]
    unfold portCount
    rw [eq]
    simp [card_insert_of_not_mem,ij]
  have mask :
      (boundary (attach G P p r) (Sum.elim c (fun _ => !b))).card=4 := by
    rw [attach_boundary,boundary_const,mismatch_const, two,pn]
  obtain ⟨k,small⟩ := strong (Sum.elim c (fun _ => !b)) mask.le
  have same : k = b := by
    by_contra ne
    have nk : (!b) = k := by
      cases b <;> cases k <;> first | rfl | exact (ne rfl).elim
    have impossible := small (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) nk nk nk
    simp at impossible
  have only (x : V) (hx : c x=b) : x=p i ∨ x=p j := by
    subst k
    rcases small (Sum.inl x) (Sum.inl (p i)) (Sum.inl (p j)) hx uu vv with h|h|h
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr (Sum.inl_injective h)
    · exact (uv (Sum.inl_injective h)).elim
  have hd (a : Port) : G.degree (p a)=2 := by
    have h := cub (p a)
    rw [attach_degree_outside,fiber_one] at h
    omega
  by_cases edge : G.Adj (p i) (p j)
  · exact edge
  · have huge := orient_big_cut c b uv uu vv only (hd i) (hd j) edge
    omega

private theorem leaf_ports (t : Fin 3) (leaf : t≠1) :
    (t=0 ∧ ∀ i,pathRoot i=t ↔ i=2 ∨ i=3) ∨
    (t=2 ∧ ∀ i,pathRoot i=t ↔ i=1 ∨ i=4) := by
  revert t
  decide

/-- A cap with fixed two-plus-two grouping is valid whenever its
paired exterior contacts are not adjacent, in the cyclic-five
input class. -/
theorem good_pentagon_cap_of_cyclic5 [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : SimpleGraph (Fin 5)} {p : Port ↪ V}
    {r : Port → Fin 5} [DecidableRel (attach G P p r).Adj]
    (normal : SmallTrivial (attach G P p r))
    (strong : SmallFourTrivial (attach G P p r))
    (cub : ∀ x,(attach G P p r).degree x=3)
    (p14 : ¬G.Adj (p 1) (p 4)) (p23 : ¬G.Adj (p 2) (p 3)) :
    SmallTrivial (pathCap G p) := by
  have laws := outside_law_of_attachment (by decide : 1<Fintype.card (Fin 5))
    normal (min_three_of_small_trivial cub normal)
  apply good_path_cap_of_no_leaf_split laws
  intro c t b leaf two fit
  rcases leaf_ports t leaf with ⟨_,a⟩|⟨_,a⟩
  · exact p23 (cyclic5_bad_pair_requires_edge strong (fun x=>cub (Sum.inl x))
      c b (by decide) two (fun i => (fit i).trans (a i)))
  · exact p14 (cyclic5_bad_pair_requires_edge strong (fun x=>cub (Sum.inl x))
      c b (by decide) two (fun i => (fit i).trans (a i)))

#print axioms cyclic5_bad_pair_requires_edge
#print axioms good_pentagon_cap_of_cyclic5

#print axioms path_cap_cubic
#print axioms bad_path_cap_profile
#print axioms good_path_cap_of_no_leaf_split

end
end KelmansCactus.AtomicBridge.PentagonCap
