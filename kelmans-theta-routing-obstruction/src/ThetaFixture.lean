import PentagonCap
import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaFixture
open SquareCap (boundary FactorOn IsTile omitEdge)
open PentagonCap (SmallFourTrivial)

abbrev X := Fin 16

def es : List (X × X) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5),(0,6),(3,6),
   (1,7),(2,8),(4,9),(6,10),(5,11),(8,11),(9,10),
   (7,12),(12,13),(13,14),(14,15),(7,15),(8,12),(11,14),(9,13),(10,15)]

private theorem sorted : ∀ x y : X, (x,y)∈es → x<y := by decide
private theorem nodup : es.Nodup := by decide

def graph : SimpleGraph X where
  Adj a b := (a,b)∈es ∨ (b,a)∈es
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless x h := not_lt_of_ge le_rfl (sorted x x (h.elim id id))

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈es ∨ (b,a)∈es))

theorem cubic : ∀ x,graph.degree x=3 := by decide

private def orient (c : X→Bool) (a b : X) : X×X := if c a then (a,b) else (b,a)

private theorem boundary_eq (c : X→Bool) :
    (boundary graph c).card = es.countP (fun e=>c e.1 != c e.2) := by
  classical
  let S := es.toFinset.filter (fun e=>c e.1≠c e.2)
  let o (e : X×X) := orient c e.1 e.2
  have shape : boundary graph c = S.image o := by
    ext ⟨u,v⟩
    have m : (u,v)∈boundary graph c ↔ c u=true ∧ c v=false ∧ graph.Adj u v := by
      simp [boundary]
    constructor
    · intro h
      obtain ⟨ho,hc,ed⟩ := m.mp h
      change (u,v)∈es ∨ (v,u)∈es at ed
      rcases ed with a|b
      · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨List.mem_toFinset.mpr a,by simp [ho,hc]⟩,
          by simp [o,orient,ho]⟩
      · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨List.mem_toFinset.mpr b,by simp [ho,hc]⟩,
          by simp [o,orient,hc]⟩
    · intro h
      obtain ⟨⟨u',v'⟩,hs,eq⟩ := mem_image.mp h
      obtain ⟨he,nd⟩ := mem_filter.mp hs
      have adj : graph.Adj u' v' := Or.inl (List.mem_toFinset.mp he)
      change c u' ≠ c v' at nd
      have mm (x y : X) : (x,y)∈boundary graph c ↔ c x=true ∧ c y=false ∧ graph.Adj x y := by
        simp [boundary]
      have useful : o (u',v') ∈ boundary graph c := by
        cases eu : c u' <;> cases ev : c v'
        · exact (nd (eu.trans ev.symm)).elim
        · exact (mm v' u').mpr ⟨ev,eu,adj.symm⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (mm u' v').mpr ⟨eu,ev,adj⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (nd (eu.trans ev.symm)).elim
      exact eq ▸ useful
  have used (e : X×X) (h : e∈S) : e.1<e.2 :=
    sorted e.1 e.2 (List.mem_toFinset.mp (mem_filter.mp h).1)
  have inj : Set.InjOn o (↑S : Set (X×X)) := by
    intro a ha b hb eq
    have na : a.1<a.2 := used a ha
    have nb : b.1<b.2 := used b hb
    have cancel (h : a = b.swap) : False := by
      rw [h] at na
      exact (not_lt_of_ge (le_of_lt nb)) na
    have ca : o a=a ∨ o a=a.swap := by
      rcases a with ⟨x,y⟩
      cases z : c x <;> simp [o,orient,z]
    have cb : o b=b ∨ o b=b.swap := by
      rcases b with ⟨x,y⟩
      cases z : c x <;> simp [o,orient,z]
    rcases ca with p|p <;> rcases cb with q|q <;> rw [p,q] at eq
    · exact eq
    · exact (cancel eq).elim
    · exact (cancel (by simpa only [Prod.swap_swap] using congrArg Prod.swap eq)).elim
    · simpa only [Prod.swap_swap] using congrArg Prod.swap eq
  rw [shape,card_image_of_injOn inj,List.countP_eq_length_filter]
  have same : S = (es.filter (fun e=>c e.1 != c e.2)).toFinset := by
    ext z
    simp [S,and_comm]
  rw [same]
  exact List.toFinset_card_of_nodup (nodup.filter _)

private theorem flip_count (c : X→Bool) :
    (boundary graph (fun i=> !(c i))).card=(boundary graph c).card := by
  rw [boundary_eq,boundary_eq]
  have eq : (fun e : X×X => (!(c e.1)) != (!(c e.2))) =
      (fun e : X×X=>c e.1 != c e.2) := by
    funext e
    cases c e.1 <;> cases c e.2 <;> rfl
  rw [eq]

abbrev Partial := X→Option Bool
def pCross (c : Partial) (e : X×X) : Bool :=
  match c e.1,c e.2 with
  | some a,some b => a != b
  | _,_ => false
def possible (c : Partial) (b : Bool) (i : X) : Bool := c i != some (!b)
def stop (c : Partial) : Bool :=
  (es.countP (pCross c) >=5) ||
  ((List.finRange 16).countP (possible c true) <=2) ||
  ((List.finRange 16).countP (possible c false) <=2)
def update (c : Partial) (x : X) (b : Bool) : Partial :=
  fun i => if i=x then some b else c i
def cert : List X → Partial → Bool
  | [],c => stop c
  | x::xs,c => if stop c then true else cert xs (update c x false) && cert xs (update c x true)
def base : Partial := fun i=>if i=15 then some false else none
def order : List X := (List.finRange 15).map Fin.castSucc
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem reflected : cert order base = true := by decide
private theorem count_ones {c : X→Bool} {b : Bool}
    (small : (List.finRange 16).countP (fun x => c x == b) ≤ 2) :
    ∀ x y z : X, c x=b → c y=b → c z=b → x=y∨x=z∨y=z := by
  intro x y z a d f
  by_cases xy : x=y
  · exact Or.inl xy
  by_cases xz : x=z
  · exact Or.inr (Or.inl xz)
  by_cases yz : y=z
  · exact Or.inr (Or.inr yz)
  exfalso
  let S := (List.finRange 16).filter (fun x=>c x == b)
  have vs : ∀ x : X, x∈S.toFinset ↔ c x=b := by simp [S]
  have low : ({x,y,z}:Finset X) ⊆ S.toFinset := by
    intro k kh
    simp only [mem_insert,mem_singleton] at kh
    rcases kh with rfl|rfl|rfl
    · exact (vs _).mpr a
    · exact (vs _).mpr d
    · exact (vs _).mpr f
  have count := card_le_card low
  have a3 : ({x,y,z}:Finset X).card=3 := by simp [card_insert_of_not_mem,xy,xz,yz]
  have noDup : S.Nodup := (List.nodup_finRange 16).filter _
  rw [a3,List.toFinset_card_of_nodup noDup,←List.countP_eq_length_filter] at count
  omega


def Extends (P : Partial) (c : X→Bool) : Prop := ∀ x b, P x=some b → c x=b

private theorem count_mono {T : Type*} {a b : T→Bool}
    (imp : ∀ x,a x=true→b x=true) (L : List T) : L.countP a ≤ L.countP b := by
  induction L with
  | nil => simp
  | cons x xs i =>
    rw [List.countP_cons,List.countP_cons]
    cases xa : a x <;> cases xb : b x
    · simpa [xa,xb] using i
    · simp [xa,xb]; omega
    · exact (by simpa [xb] using imp x xa : False).elim
    · simpa [xa,xb] using i

private theorem stop_sound {P : Partial} {c : X→Bool}
    (ext : Extends P c) (h : stop P = true) :
    5 ≤ (boundary graph c).card ∨
      ∃ b : Bool, (List.finRange 16).countP (fun x => c x==b) ≤ 2 := by
  simp only [stop,Bool.or_eq_true,decide_eq_true_eq] at h
  have lower (e : X×X) (has : pCross P e=true) : (c e.1 != c e.2)=true := by
    cases e1 : P e.1 <;> cases e2 : P e.2 <;> try simp [pCross,e1,e2] at has
    rename_i y z
    rw [ext _ _ e1,ext _ _ e2]
    simpa using has
  have upper (b : Bool) (x : X) (hx : (c x==b)=true) : possible P b x=true := by
    have xb := beq_iff_eq.mp hx
    have ne : P x≠some (!b) := by
      intro eq
      have clash := xb.symm.trans (ext x (!b) eq)
      cases b <;> simp at clash
    simpa [possible] using ne
  rcases h with (cut|trueSmall)|falseSmall
  · left
    rw [boundary_eq]
    exact cut.trans (count_mono lower es)
  · right
    exact ⟨true,(count_mono (upper true) (List.finRange 16)).trans trueSmall⟩
  · right
    exact ⟨false,(count_mono (upper false) (List.finRange 16)).trans falseSmall⟩

private theorem cert_sound (L : List X) {P : Partial} {c : X→Bool}
    (ext : Extends P c) (h : cert L P=true) :
    5 ≤ (boundary graph c).card ∨
      ∃ b : Bool, (List.finRange 16).countP (fun x=>c x==b)≤2 := by
  induction L generalizing P with
  | nil => exact stop_sound ext h
  | cons x xs ih =>
    cases valid : stop P
    · have next : cert xs (update P x false)=true ∧ cert xs (update P x true)=true := by
        simpa [cert,valid] using h
      have sub (b : Bool) (xb : c x=b) : Extends (update P x b) c := by
        intro y q hy
        by_cases eq : y=x
        · subst y
          have eq2 : b=q := by simpa [update] using hy
          exact xb.trans eq2
        · have e : P y=some q := by simpa [update,eq] using hy
          exact ext y q e
      cases e : c x
      · exact ih (sub false e) next.1
      · exact ih (sub true e) next.2
    · exact stop_sound ext valid

private theorem normalized_small (c : X→Bool) (last : c 15=false)
    (budget : (boundary graph c).card≤4) :
    ∃ b : Bool, ∀ x y z : X,c x=b → c y=b → c z=b → x=y∨x=z∨y=z := by
  have extend : Extends base c := by
    intro x b e
    by_cases eq : x=15
    · subst x
      have b0 : false=b := by simpa [base] using e
      exact last.trans b0
    · simp [base,eq] at e
  rcases cert_sound order extend reflected with many|⟨b,count⟩
  · omega
  · exact ⟨b,count_ones count⟩

theorem cyclic_five_cut_condition : SmallFourTrivial graph := by
  intro c h
  by_cases last : c 15 = false
  · exact normalized_small c last h
  · let flip : X→Bool := fun i=> !(c i)
    have b : flip 15=false := by cases e : c 15 <;> simp_all [flip]
    have j : (boundary graph flip).card≤4 := (flip_count c).le.trans h
    obtain ⟨v,small⟩ := normalized_small flip b j
    refine ⟨!v,?_⟩
    intro x y z hx hy hz
    apply small x y z <;> cases v <;> simp_all [flip]

def target : SimpleGraph X := omitEdge graph 5 0

instance : DecidableRel target.Adj := by
  intro a b
  change Decidable (graph.Adj a b ∧ ¬ ((a=5 ∧ b=0) ∨ (a=0 ∧ b=5)))
  infer_instance

private instance (s : Finset X) : Decidable (IsTile target s) := by
  unfold IsTile
  infer_instance

def partition : Finset (Finset X) :=
  {{0,1,2},{3,4,5},{7,12,15},{8,11,14},{9,10,13}}

/-- Both critical exterior pairs are genuine edges. Neither says
anything about absence of a factor in the original target. -/
theorem paired_contacts_adjacent : graph.Adj 8 11 ∧ graph.Adj 9 10 := by decide

/-- The witness is emphatically not a counterexample to F2: the
original graph minus root 6 and edge 5–0 has this explicit factor. -/
theorem target_has_factor : FactorOn target (univ.erase 6) := by
  refine ⟨partition,?_,?_,by decide⟩
  · intro a ma
    simp only [partition,mem_insert,mem_singleton] at ma
    rcases ma with rfl|rfl|rfl|rfl|rfl <;> decide
  · intro a ma b mb ne
    simp only [partition,mem_insert,mem_singleton] at ma mb
    rcases ma with rfl|rfl|rfl|rfl|rfl <;> rcases mb with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact (ne rfl).elim | decide

private def pairColor (a b z : X) : Bool := decide (z=a∨z=b)

private theorem pair_cut_list : ∀ a b : X, a≠b →
    4≤es.countP (fun e=>pairColor a b e.1 != pairColor a b e.2) := by decide

/-- The fixture also satisfies the project's exact cyclic-four
cut condition, and hence its usual 3-vertex-connectivity definition. -/
theorem cyclic_four_cut_condition : SquareCap.SmallTrivial graph := by
  intro c budget
  obtain ⟨b,few⟩ := cyclic_five_cut_condition c (by omega)
  have one : ∀ x y : X,c x=b → c y=b → x=y := by
    intro x y hx hy
    by_contra ne
    have col (z : X) : c z=b ↔ z=x∨z=y := by
      constructor
      · intro zr
        rcases few z x y zr hx hy with e|e|e
        · exact Or.inl e
        · exact Or.inr e
        · exact (ne e).elim
      · rintro (rfl|rfl)
        · exact hx
        · exact hy
    have low := pair_cut_list x y ne
    rw [←boundary_eq] at low
    have pick (z : X) : pairColor x y z=true ↔ c z=b := by simpa [pairColor] using (col z).symm
    have flipEq : (boundary graph (pairColor x y)).card=(boundary graph c).card := by
      cases b
      · have eq : pairColor x y = fun z=> !(c z) := by
          funext z
          apply Bool.eq_iff_iff.mpr
          simpa using pick z
        rw [eq,flip_count]
      · have eq : pairColor x y=c := by
          funext z
          exact Bool.eq_iff_iff.mpr (pick z)
        rw [eq]
    omega
  cases b
  · exact Or.inr one
  · exact Or.inl one

theorem three_connected : SquareCap.ThreeConnected graph :=
  SquareCap.three_connected_of_small_trivial graph cubic (by decide) cyclic_four_cut_condition

private theorem common_bound : ∀ x y : X,x≠y →
    ((graph.neighborFinset x)∩(graph.neighborFinset y)).card≤1 := by decide

/-- A second independently finite-audited description of the fixture:
it has no simple four-cycle. -/
theorem no_four_cycle : ∀ a b c d : X, graph.Adj a b → graph.Adj b c →
    graph.Adj c d → graph.Adj d a → a=c∨b=d := by
  intro a b c d ab bc cd da
  by_cases ac : a=c
  · exact Or.inl ac
  by_cases bd : b=d
  · exact Or.inr bd
  exfalso
  have bb : b∈((graph.neighborFinset a)∩(graph.neighborFinset c)) :=
    mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr ab,(mem_neighborFinset _ _ _).mpr bc.symm⟩
  have dd : d∈((graph.neighborFinset a)∩(graph.neighborFinset c)) :=
    mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr da.symm,(mem_neighborFinset _ _ _).mpr cd⟩
  exact bd (card_le_one.mp (common_bound a c ac) _ bb _ dd)

#print axioms cyclic_four_cut_condition
#print axioms three_connected
#print axioms no_four_cycle

#print axioms paired_contacts_adjacent
#print axioms target_has_factor
#print axioms cubic
#print axioms reflected
#print axioms cyclic_five_cut_condition
end KelmansCactus.AtomicBridge.ThetaFixture
