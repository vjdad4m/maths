import T2AvoidCounterexample

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.T2AvoidCyclicFour
open SquareCap (boundary SmallTrivial)
open T2AvoidCounterexample (V G edges domain_shape)
abbrev X := V
private theorem sorted : ∀ a b : X,(a,b)∈edges→a<b := by decide
private theorem nodup : edges.Nodup := by decide

private def orient (c : X→Bool) (a b : X) : X×X := if c a then (a,b) else (b,a)

private theorem boundary_eq (c : X→Bool) :
    (boundary G c).card = edges.countP (fun e=>c e.1 != c e.2) := by
  classical
  let S := edges.toFinset.filter (fun e=>c e.1≠c e.2)
  let o (e : X×X) := orient c e.1 e.2
  have shape : boundary G c = S.image o := by
    ext ⟨u,v⟩
    have m : (u,v)∈boundary G c ↔ c u=true ∧ c v=false ∧ G.Adj u v := by
      simp [boundary]
    constructor
    · intro h
      obtain ⟨ho,hc,ed⟩ := m.mp h
      change (u,v)∈edges ∨ (v,u)∈edges at ed
      rcases ed with a|b
      · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨List.mem_toFinset.mpr a,by simp [ho,hc]⟩,
          by simp [o,orient,ho]⟩
      · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨List.mem_toFinset.mpr b,by simp [ho,hc]⟩,
          by simp [o,orient,hc]⟩
    · intro h
      obtain ⟨⟨u',v'⟩,hs,eq⟩ := mem_image.mp h
      obtain ⟨he,nd⟩ := mem_filter.mp hs
      have adj : G.Adj u' v' := Or.inl (List.mem_toFinset.mp he)
      change c u' ≠ c v' at nd
      have mm (x y : X) : (x,y)∈boundary G c ↔ c x=true ∧ c y=false ∧ G.Adj x y := by
        simp [boundary]
      have useful : o (u',v') ∈ boundary G c := by
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
  have same : S = (edges.filter (fun e=>c e.1 != c e.2)).toFinset := by
    ext z
    simp [S,and_comm]
  rw [same]
  exact List.toFinset_card_of_nodup (nodup.filter _)

private theorem flip_count (c : X→Bool) :
    (boundary G (fun i=> !(c i))).card=(boundary G c).card := by
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
  (edges.countP (pCross c) >=4) ||
  ((List.finRange 14).countP (possible c true) <=1) ||
  ((List.finRange 14).countP (possible c false) <=1)
def update (c : Partial) (x : X) (b : Bool) : Partial :=
  fun i => if i=x then some b else c i
def cert : List X → Partial → Bool
  | [],c => stop c
  | x::xs,c => if stop c then true else cert xs (update c x false) && cert xs (update c x true)
def base : Partial := fun i=>if i=13 then some false else none
def extend4 (a b c d : Bool) : Partial :=
  update (update (update (update base 12 a) 3 b) 2 c) 7 d
def order : List X := [1,5,4,10,6,11,9,8,0]
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem reflected (a b c d : Bool) :
    cert order (extend4 a b c d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem count_ones {c : X→Bool} {b : Bool}
    (small : (List.finRange 14).countP (fun x => c x == b) ≤ 1) :
    ∀ x y : X,c x=b→c y=b→x=y := by
  let S := (List.finRange 14).filter (fun x=>c x==b)
  have few : S.toFinset.card≤1 := by
    rw [List.toFinset_card_of_nodup ((List.nodup_finRange 14).filter _),
      ←List.countP_eq_length_filter]
    exact small
  intro x y cx cy
  exact (card_le_one.mp few) x (by simp [S,cx]) y (by simp [S,cy])

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
    4 ≤ (boundary G c).card ∨
      ∃ b : Bool, (List.finRange 14).countP (fun x => c x==b) ≤ 1 := by
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
    exact cut.trans (count_mono lower edges)
  · right
    exact ⟨true,(count_mono (upper true) (List.finRange 14)).trans trueSmall⟩
  · right
    exact ⟨false,(count_mono (upper false) (List.finRange 14)).trans falseSmall⟩

private theorem cert_sound (L : List X) {P : Partial} {c : X→Bool}
    (ext : Extends P c) (h : cert L P=true) :
    4 ≤ (boundary G c).card ∨
      ∃ b : Bool, (List.finRange 14).countP (fun x=>c x==b)≤1 := by
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


private theorem normalized_small (c : X→Bool) (last : c 13=false)
    (budget : (boundary G c).card≤3) :
    ∃ b : Bool,∀ x y : X,c x=b→c y=b→x=y := by
  have extend : Extends base c := by
    intro x b e
    by_cases eq : x=13
    · subst x
      have b0 : false=b := by simpa [base] using e
      exact last.trans b0
    · simp [base,eq] at e
  have ext4 : Extends (extend4 (c 12) (c 3) (c 2) (c 7)) c := by
    intro x b h
    by_cases e3 : x=7
    · subst x
      simpa [extend4,update] using h
    by_cases e2 : x=2
    · subst x
      simpa [extend4,update] using h
    by_cases e1 : x=3
    · subst x
      simpa [extend4,update] using h
    by_cases e0 : x=12
    · subst x
      simpa [extend4,update] using h
    exact extend x b (by simpa [extend4,update,e3,e2,e1,e0] using h)
  rcases cert_sound order ext4 (reflected (c 12) (c 3) (c 2) (c 7)) with many|⟨b,count⟩
  · omega
  · exact ⟨b,count_ones count⟩

theorem cyclic_four : SmallTrivial G := by
  have raw (c : X→Bool) (h : (boundary G c).card≤3) :
      ∃ b : Bool,∀ x y : X,c x=b→c y=b→x=y := by
    by_cases last : c 13 = false
    · exact normalized_small c last h
    · let flip : X→Bool := fun i=> !(c i)
      have b : flip 13=false := by cases e : c 13 <;> simp_all [flip]
      have j : (boundary G flip).card≤3 := (flip_count c).le.trans h
      obtain ⟨v,small⟩ := normalized_small flip b j
      refine ⟨!v,?_⟩
      intro x y hx hy
      apply small x y <;> cases v <;> simp_all [flip]
  intro c h
  obtain ⟨b,small⟩ := raw c h
  cases b
  · exact Or.inr small
  · exact Or.inl small

theorem three_connected : SquareCap.ThreeConnected G :=
  SquareCap.three_connected_of_small_trivial G domain_shape.1 (by decide) cyclic_four

#print axioms cyclic_four
#print axioms three_connected

end KelmansCactus.AtomicBridge.T2AvoidCyclicFour
