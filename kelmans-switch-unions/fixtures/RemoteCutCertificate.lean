import SquareCapGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteCutCertificate
open SquareCap (boundary)

/-- Numeric edge representation, sorted inside each edge, no repeats. -/
structure Table (n : ℕ) where
  edges : List (Fin n×Fin n)
  sorted : ∀ a b,(a,b)∈edges→a<b
  nodup : edges.Nodup

variable {n : ℕ}
local notation "X" => Fin n
variable (E : Table n)

namespace Table

def graph : SimpleGraph X where
  Adj a b := (a,b)∈E.edges∨(b,a)∈E.edges
  symm := fun _ _ e=>e.elim Or.inr Or.inl
  loopless a h := lt_irrefl _ (E.sorted a a (h.elim id id))

instance : DecidableRel E.graph.Adj :=
  fun a b=>inferInstanceAs (Decidable ((a,b)∈E.edges∨(b,a)∈E.edges))

private def orient (c : X→Bool) (a b : X) : X×X := if c a then (a,b) else (b,a)

private theorem boundary_eq (c : X→Bool) :
    (boundary E.graph c).card = E.edges.countP (fun e=>c e.1 != c e.2) := by
  classical
  let S := E.edges.toFinset.filter (fun e=>c e.1≠c e.2)
  let o (e : X×X) := orient c e.1 e.2
  have shape : boundary E.graph c = S.image o := by
    ext ⟨u,v⟩
    have m : (u,v)∈boundary E.graph c ↔ c u=true ∧ c v=false ∧ E.graph.Adj u v := by
      simp [boundary]
    constructor
    · intro h
      obtain ⟨ho,hc,ed⟩ := m.mp h
      change (u,v)∈E.edges ∨ (v,u)∈E.edges at ed
      rcases ed with a|b
      · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨List.mem_toFinset.mpr a,by simp [ho,hc]⟩,
          by simp [o,orient,ho]⟩
      · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨List.mem_toFinset.mpr b,by simp [ho,hc]⟩,
          by simp [o,orient,hc]⟩
    · intro h
      obtain ⟨⟨u',v'⟩,hs,eq⟩ := mem_image.mp h
      obtain ⟨he,nd⟩ := mem_filter.mp hs
      have adj : E.graph.Adj u' v' := Or.inl (List.mem_toFinset.mp he)
      change c u' ≠ c v' at nd
      have mm (x y : X) : (x,y)∈boundary E.graph c ↔ c x=true ∧ c y=false ∧ E.graph.Adj x y := by
        simp [boundary]
      have useful : o (u',v') ∈ boundary E.graph c := by
        cases eu : c u' <;> cases ev : c v'
        · exact (nd (eu.trans ev.symm)).elim
        · exact (mm v' u').mpr ⟨ev,eu,adj.symm⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (mm u' v').mpr ⟨eu,ev,adj⟩ |> fun hh => by simpa [o,orient,eu] using hh
        · exact (nd (eu.trans ev.symm)).elim
      exact eq ▸ useful
  have used (e : X×X) (h : e∈S) : e.1<e.2 :=
    E.sorted e.1 e.2 (List.mem_toFinset.mp (mem_filter.mp h).1)
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
  have same : S = (E.edges.filter (fun e=>c e.1 != c e.2)).toFinset := by
    ext z
    simp [S,and_comm]
  rw [same]
  exact List.toFinset_card_of_nodup (E.nodup.filter _)


private theorem flip_count (c : X→Bool) :
    (boundary E.graph (fun i=> !(c i))).card=(boundary E.graph c).card := by
  rw [E.boundary_eq,E.boundary_eq]
  have eq : (fun e : X×X => (!(c e.1)) != (!(c e.2))) =
      (fun e : X×X=>c e.1 != c e.2) := by
    funext e
    cases c e.1 <;> cases c e.2 <;> rfl
  rw [eq]

abbrev Shade (n : ℕ) := Fin n→Option Bool
def pCross (c : Shade n) (e : X×X) : Bool :=
  match c e.1,c e.2 with
  | some a,some b => a != b
  | _,_ => false
def possible (c : Shade n) (b : Bool) (i : X) : Bool := c i != some (!b)
def stop (k s : ℕ) (c : Shade n) : Bool :=
  (E.edges.countP (pCross c) >=k) ||
  ((List.finRange n).countP (possible c true) <=s) ||
  ((List.finRange n).countP (possible c false) <=s)
def update (c : Shade n) (x : X) (b : Bool) : Shade n :=
  fun i => if i=x then some b else c i
def cert (k s : ℕ) : List X → Shade n → Bool
  | [],c => E.stop k s c
  | x::xs,c => if E.stop k s c then true else cert k s xs (update c x false) && cert k s xs (update c x true)
def Extends (P : Shade n) (c : X→Bool) : Prop := ∀ x b, P x=some b → c x=b

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

private theorem stop_sound {P : Shade n} {c : X→Bool}
    (ext : Extends P c) (h : E.stop k s P = true) :
    k ≤ (boundary E.graph c).card ∨
      ∃ b : Bool, (List.finRange n).countP (fun x => c x==b) ≤ s := by
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
    rw [E.boundary_eq]
    exact cut.trans (count_mono lower E.edges)
  · right
    exact ⟨true,(count_mono (upper true) (List.finRange n)).trans trueSmall⟩
  · right
    exact ⟨false,(count_mono (upper false) (List.finRange n)).trans falseSmall⟩

private theorem cert_sound (L : List X) {P : Shade n} {c : X→Bool}
    (ext : Extends P c) (h : E.cert k s L P=true) :
    k ≤ (boundary E.graph c).card ∨
      ∃ b : Bool, (List.finRange n).countP (fun x=>c x==b)≤s := by
  induction L generalizing P with
  | nil => exact E.stop_sound ext h
  | cons x xs ih =>
    cases valid : E.stop k s P
    · have next : E.cert k s xs (update P x false)=true ∧ E.cert k s xs (update P x true)=true := by
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
    · exact E.stop_sound ext valid



def base (root : X) : Shade n := fun v=>if v=root then some false else none

/-- A true partial-color checker certifies the exact cut bound.
Both specified color classes must have more than s vertices. -/
theorem cut_ge {k s : ℕ} {order : List X} {root : X}
    (ok : E.cert k s order (base root)=true)
    (c : X→Bool) (wide : ∀ b,s<(List.finRange n).countP (fun x=>c x==b)) :
    k≤(boundary E.graph c).card := by
  have normalized (c : X→Bool) (wide : ∀ b,s<(List.finRange n).countP (fun x=>c x==b))
      (fixed : c root=false) : k≤(boundary E.graph c).card := by
    have extend : Extends (base root) c := by
      intro x b e
      by_cases eq : x=root
      · subst x
        have b0 : false=b := by simpa [base] using e
        exact fixed.trans b0
      · simp [base,eq] at e
    rcases E.cert_sound order extend ok with yes|⟨b,tooSmall⟩
    · exact yes
    · exact False.elim ((Nat.not_le_of_lt (wide b)) tooSmall)
  by_cases fixed : c root=false
  · exact normalized c wide fixed
  · let f : X→Bool := fun x=> !(c x)
    have w (b : Bool) : s<(List.finRange n).countP (fun x=>f x==b) := by
      have eq : (fun x=>f x==b)=(fun x=>c x==(!b)) := by
        funext x
        cases hx : c x <;> cases b <;> simp [f,hx]
      rw [eq]
      apply wide
    have fr : f root=false := by cases e : c root <;> simp_all [f]
    have j := normalized f w fr
    exact (E.flip_count c) ▸ j

private theorem tiny_colour {c : X→Bool} {b : Bool}
    (few : (List.finRange n).countP (fun x=>c x==b)≤1) :
     ∀ x y : X,c x=b→c y=b→x=y := by
  let S := (List.finRange n).filter (fun x=>c x==b)
  have f : S.toFinset.card≤1 := by
    rw [List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _),
      ←List.countP_eq_length_filter]
    exact few
  intro x y cx cy
  exact (card_le_one.mp f) x (by simp [S,cx]) y (by simp [S,cy])

theorem cyclic_four {order : List X} {root : X}
    (ok : E.cert 4 1 order (base root)=true) : SquareCap.SmallTrivial E.graph := by
  intro c cut
  by_cases pos : (List.finRange n).countP (fun x=>c x==true)≤1
  · exact Or.inl (tiny_colour pos)
  · by_cases neg : (List.finRange n).countP (fun x=>c x==false)≤1
    · exact Or.inr (tiny_colour neg)
    · have many (b : Bool) : 1<(List.finRange n).countP (fun x=>c x==b) := by
        cases b
        · exact Nat.lt_of_not_ge neg
        · exact Nat.lt_of_not_ge pos
      have width := E.cut_ge ok c many
      omega

#print axioms cyclic_four

#print axioms cut_ge
end Table
end KelmansCactus.AtomicBridge.RemoteCutCertificate
