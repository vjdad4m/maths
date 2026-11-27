import ThetaRootContactCap
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaRootContactFixture
open SquareCap (boundary FactorOn IsTile omitEdge)
open PentagonCap (SmallFourTrivial)

abbrev X := Fin 10

def es : List (X×X) := [(0,3),(0,5),(0,8),(1,7),(1,8),(1,9),(2,5),(2,7),(2,9),(3,6),(3,7),(4,5),(4,6),(4,9),(6,8)]

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
  (es.countP (pCross c) >=4) ||
  ((List.finRange 10).countP (possible c true) <=1) ||
  ((List.finRange 10).countP (possible c false) <=1)
def update (c : Partial) (x : X) (b : Bool) : Partial :=
  fun i => if i=x then some b else c i
def cert : List X → Partial → Bool
  | [],c => stop c
  | x::xs,c => if stop c then true else cert xs (update c x false) && cert xs (update c x true)
def base : Partial := fun i=>if i=9 then some false else none
def extend4 (a b c d : Bool) : Partial :=
  update (update (update (update base 0 a) 1 b) 2 c) 3 d
def order : List X := [4,5,6,7,8]
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem reflected (a b c d : Bool) :
    cert order (extend4 a b c d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem count_ones {c : X→Bool} {b : Bool}
    (small : (List.finRange 10).countP (fun x=>c x==b) ≤ 1) :
    ∀ x y : X,c x=b → c y=b → x=y := by
  intro x y a d
  by_contra ne
  let S := (List.finRange 10).filter (fun v=>c v==b)
  have yes : ∀ v : X,v∈S.toFinset ↔ c v=b := by simp [S]
  have low : ({x,y}:Finset X)⊆S.toFinset := by
    intro k m
    simp only [mem_insert,mem_singleton] at m
    rcases m with rfl|rfl
    · exact (yes _).mpr a
    · exact (yes _).mpr d
  have ct := card_le_card low
  have two : ({x,y}:Finset X).card=2 := by simp [card_insert_of_not_mem,ne]
  have nd : S.Nodup := (List.nodup_finRange 10).filter _
  rw [two,List.toFinset_card_of_nodup nd,←List.countP_eq_length_filter] at ct
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
    4 ≤ (boundary graph c).card ∨
      ∃ b : Bool, (List.finRange 10).countP (fun x => c x==b) ≤ 1 := by
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
    exact ⟨true,(count_mono (upper true) (List.finRange 10)).trans trueSmall⟩
  · right
    exact ⟨false,(count_mono (upper false) (List.finRange 10)).trans falseSmall⟩

private theorem cert_sound (L : List X) {P : Partial} {c : X→Bool}
    (ext : Extends P c) (h : cert L P=true) :
    4 ≤ (boundary graph c).card ∨
      ∃ b : Bool, (List.finRange 10).countP (fun x=>c x==b)≤1 := by
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

private theorem normalized_small (c : X→Bool) (last : c 9=false)
    (budget : (boundary graph c).card≤3) :
    ∃ b : Bool, ∀ x y : X,c x=b → c y=b → x=y := by
  have extend : Extends base c := by
    intro x b e
    by_cases eq : x=9
    · subst x
      have b0 : false=b := by simpa [base] using e
      exact last.trans b0
    · simp [base,eq] at e
  have ext4 : Extends (extend4 (c 0) (c 1) (c 2) (c 3)) c := by
    intro x b h
    by_cases e3 : x=3
    · subst x
      simpa [extend4,update] using h
    by_cases e2 : x=2
    · subst x
      simpa [extend4,update] using h
    by_cases e1 : x=1
    · subst x
      simpa [extend4,update] using h
    by_cases e0 : x=0
    · subst x
      simpa [extend4,update] using h
    exact extend x b (by simpa [extend4,update,e3,e2,e1,e0] using h)
  rcases cert_sound order ext4 (reflected (c 0) (c 1) (c 2) (c 3)) with many|⟨b,count⟩
  · omega
  · exact ⟨b,count_ones count⟩

theorem cyclic_four : SquareCap.SmallTrivial graph := by
  intro c h
  have sides : ∃ b : Bool,∀ x y : X,c x=b → c y=b → x=y := by
    by_cases last : c 9=false
    · exact normalized_small c last h
    · let flip : X→Bool := fun i=> !(c i)
      have b : flip 9=false := by cases e : c 9 <;> simp_all [flip]
      have j : (boundary graph flip).card≤3 := (flip_count c).le.trans h
      obtain ⟨v,small⟩ := normalized_small flip b j
      refine ⟨!v,?_⟩
      intro x y hx hy
      apply small x y <;> cases v <;> simp_all [flip]
  rcases sides with ⟨v,hs⟩
  cases v
  · exact Or.inr hs
  · exact Or.inl hs

open PentagonProfile (Port)

abbrev Outside := Fin 9

def outsideEdges : List (Outside × Outside) :=
  [(0,5),(0,8),(1,7),(1,8),(2,5),(2,7),(3,6),(3,7),(4,5),(4,6),(6,8)]

private theorem increasing : ∀ x : Outside, (x,x)∉outsideEdges := by decide

def outside : SimpleGraph Outside where
  Adj a b := (a,b)∈outsideEdges ∨ (b,a)∈outsideEdges
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := increasing a (h.elim id id)

instance : DecidableRel outside.Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈outsideEdges ∨ (b,a)∈outsideEdges))

def ports : Port ↪ Outside :=
  ⟨fun i => ⟨i.val,by have li := i.isLt; omega⟩,fun _ _ eq=>Fin.ext (congrArg (fun x : Outside=>x.val) eq)⟩

instance : DecidableRel (ThetaCase.ambient outside ports).Adj := by
  intro a b
  cases a <;> cases b
  · exact inferInstanceAs (Decidable (outside.Adj _ _))
  · exact inferInstanceAs (Decidable (∃ i : Port, ports i = _ ∧ ThetaCase.arm i = _))
  · exact inferInstanceAs (Decidable (∃ i : Port, ports i = _ ∧ ThetaCase.arm i = _))
  · exact inferInstanceAs (Decidable (ThetaCase.theta.Adj _ _))

private def fwd : (Outside⊕Unit) → X
  | .inl i => i.castSucc
  | .inr _ => 9

private theorem fwd_bij : Function.Bijective fwd := by
  constructor
  · intro a b h
    have eq := congrArg Fin.val h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext eq)
      | inr b =>
        change a.val=9 at eq
        have hi := a.isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        change 9=b.val at eq
        have hi := b.isLt
        omega
      | inr b =>
        cases a
        cases b
        rfl
  · intro t
    by_cases h : t.val<9
    · exact ⟨Sum.inl ⟨t.val,h⟩,rfl⟩
    · have l := t.isLt
      exact ⟨Sum.inr (),Fin.ext (by change 9=t.val; omega)⟩

open SquareCap (SmallTrivial)
open ThetaRootContactSplice (stem)

def candidate : SimpleGraph (Outside⊕Unit) :=
  ThetaRootContactCap.cap outside ports 0 (by decide)

instance : DecidableRel candidate.Adj :=
  inferInstanceAs (DecidableRel (ThetaRootContactCap.cap outside ports 0 (by decide)).Adj)

noncomputable def exact_cap : candidate ≃g graph where
  toEquiv := Equiv.ofBijective fwd fwd_bij
  map_rel_iff' := by
    intro a b
    have reflected : ∀ a b : Outside⊕Unit,graph.Adj (fwd a) (fwd b) ↔ candidate.Adj a b := by decide
    exact reflected a b

private theorem boundary_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (c : A → Bool) :
    (boundary H c).card = (boundary K (c ∘ e.symm)).card := by
  classical
  have memA (z : A×A) : z∈boundary H c ↔ c z.1=true ∧ c z.2=false ∧ H.Adj z.1 z.2 := by
    simp [boundary]
  have memB (z : B×B) : z∈boundary K (c ∘ e.symm) ↔
      c (e.symm z.1)=true ∧ c (e.symm z.2)=false ∧ K.Adj z.1 z.2 := by simp [boundary]
  apply card_bij (fun z _ => (e z.1,e z.2))
  · intro z h
    obtain ⟨f,t,u⟩ := (memA z).mp h
    exact (memB _).mpr ⟨by simpa using f,by simpa using t,e.map_adj_iff.mpr u⟩
  · intro a _ b _ h
    exact Prod.ext (e.toEquiv.injective (congrArg Prod.fst h)) (e.toEquiv.injective (congrArg Prod.snd h))
  · intro z h
    obtain ⟨f,t,u⟩ := (memB z).mp h
    exact ⟨(e.symm z.1,e.symm z.2),(memA _).mpr ⟨f,t,e.symm.map_adj_iff.mpr u⟩,
      Prod.ext (e.toEquiv.apply_symm_apply _) (e.toEquiv.apply_symm_apply _)⟩

private theorem small_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallTrivial K) :
    SmallTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  rcases h (c ∘ e.symm) near with ts|fs
  · left
    intro x y hx hy
    apply e.toEquiv.injective
    exact ts (e x) (e y) (by simpa using hx) (by simpa using hy)
  · right
    intro x y hx hy
    apply e.toEquiv.injective
    exact fs (e x) (e y) (by simpa using hx) (by simpa using hy)


theorem candidate_cyclic_four : SmallTrivial candidate := small_iso exact_cap cyclic_four

theorem no_opposite_pair :
    ¬outside.Adj (ports 0) (ports 2) ∧ ¬outside.Adj (ports 1) (ports 4) := by decide

theorem cubic_original : ∀ x,(ThetaCase.ambient outside ports).degree x=3 := by decide

theorem actual_edges : outside.Adj (ports 0) 5 ∧ ¬outside.Adj (ports 0) (ports 3) := by decide

def restricted : SimpleGraph (Outside⊕Unit) := omitEdge candidate stem (Sum.inl 2)

instance : DecidableRel restricted.Adj := fun a b =>
  inferInstanceAs (Decidable (candidate.Adj a b ∧
    ¬((a=stem ∧ b=Sum.inl 2)∨(a=Sum.inl 2∧b=stem))))

private instance (s : Finset (Outside⊕Unit)) : Decidable (IsTile restricted s) := by
  unfold IsTile
  infer_instance

def partition : Finset (Finset (Outside⊕Unit)) :=
  {{Sum.inl 3,Sum.inl 6,Sum.inl 8},{Sum.inl 2,Sum.inl 5,Sum.inl 4},
    {Sum.inl 7,Sum.inl 1,stem}}

theorem cap_factor : FactorOn restricted (univ.erase (Sum.inl 0)) := by
  refine ⟨partition,?_,?_,by decide⟩
  · intro a ma
    simp only [partition,mem_insert,mem_singleton] at ma
    rcases ma with rfl|rfl|rfl <;> decide
  · intro a ma b mb ne
    simp only [partition,mem_insert,mem_singleton] at ma mb
    rcases ma with rfl|rfl|rfl <;> rcases mb with rfl|rfl|rfl
    all_goals first | exact (ne rfl).elim | decide

/-- The previous live/live four-cap obstruction admits the
root-contact route on a different genuine omitted edge, 7–12 in
the original numbered fixture. Lift the smaller checked factor. -/
theorem lifted_from_cap :
    FactorOn (omitEdge (ThetaCase.ambient outside ports) (Sum.inl 0) (Sum.inl 5))
      (univ.erase (Sum.inr 6)) :=
  ThetaRootContactCap.lift_certified_cap (G:=outside) (p:=ports) false false 5 cap_factor

#print axioms exact_cap
#print axioms no_opposite_pair
#print axioms cubic_original
#print axioms actual_edges
#print axioms candidate_cyclic_four
#print axioms cap_factor
#print axioms lifted_from_cap
end KelmansCactus.AtomicBridge.ThetaRootContactFixture
