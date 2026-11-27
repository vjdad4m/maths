import SmallSeparator189
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
namespace FourOrder12
open Finset
abbrev Bits := Fin 6 → Bool

def dir (m : Bits) (e f g : Bool) (u v : Fin 12) : Bool :=
  let a := u.val
  let b := v.val
  (decide (b=a+1 ∧ b≤10)) ||
  (decide ((a=1 ∨ a=9) ∧ b=11)) ||
  (if h : a=0 ∧ 3≤b ∧ b≤8 then m ⟨b-3,by omega⟩ else false) ||
  (if h : b=10 ∧ 2≤a ∧ a≤7 then !(m ⟨a-2,by omega⟩) else false) ||
  (decide (a=1 ∧ b=9) && e) ||
  (decide (a=1 ∧ b=8) && f) ||
  (decide (a=2 ∧ b=9) && g)

def edge (m : Bits) (e f g : Bool) (u v : Fin 12) : Bool :=
  dir m e f g u v || dir m e f g v u

def d2Set (m : Bits) (e f g : Bool) (x : Fin 12) : Finset (Fin 12) :=
  univ.filter fun y =>
    y≠x ∧ !(edge m e f g x y) = true ∧ ∃ z : Fin 12, edge m e f g x z = true ∧ edge m e f g z y=true

def lastThree (i : Fin 6) : Bool := Nat.ble 3 i.val


def bits (b0 b1 b2 b3 b4 b5 : Bool) (k : Fin 6) : Bool :=
  if k.val=0 then b0 else if k.val=1 then b1 else if k.val=2 then b2 else if k.val=3 then b3 else if k.val=4 then b4 else b5

def check (m : Bits) (e f g : Bool) : Prop :=
  (univ.filter fun i : Fin 6 => m i = true).card=3 →
  (e || f)=true → (e || g)=true →
  (d2Set m e f g 0).card≤4 → (d2Set m e f g 10).card≤4 →
  (d2Set m e f g 1).card≤4 → (d2Set m e f g 9).card≤4 →
  (∀ i : Fin 6, m i=lastThree i) ∧ e=true ∧ f=true ∧ g=true

noncomputable instance chk (m : Bits) (e f g : Bool) : Decidable (check m e f g) := by
  unfold check
  infer_instance

set_option maxRecDepth 36000 in
set_option maxHeartbeats 5000000 in
theorem tiny (m : Bits) (e f g : Bool) : check m e f g := by
  have tt : ∀ b0 b1 b2 b3 b4 b5 e f g : Bool, check (bits b0 b1 b2 b3 b4 b5) e f g := by decide
  have eq : bits (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)=m := by
    funext i
    fin_cases i <;> rfl
  simpa only [eq] using tt (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) e f g

#print axioms tiny


section Lift
set_option linter.unusedSectionVars false
open SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem construct_walk (x : V) (l : List V) (h : List.Chain' G.Adj (x::l)) :
    ∃ y,∃ p : G.Walk x y,p.support=x::l := by
  induction l generalizing x with
  | nil => exact ⟨x,.nil,rfl⟩
  | cons a l ih =>
    obtain ⟨y,p,hp⟩ := ih a h.tail
    exact ⟨y,.cons h.rel_head p,by simp [hp]⟩

theorem lift (hc : G.Connected) (cap : ∀ x,(DistanceTwo G x).card≤4)
    (m : Bits) (e f g : Bool) (φ : Fin 12 → V)
    (injection : Function.Injective φ) (onto : Function.Surjective φ)
    (left : (univ.filter fun i : Fin 6 => m i = true).card=3)
    (sf : (e || f)=true) (tg : (e || g)=true)
    (edges : ∀ u v, edge m e f g u v=true → G.Adj (φ u) (φ v))
    (centers : ∀ u∈({0,1,9,10}:Finset (Fin 12)), ∀ v, G.Adj (φ u) (φ v) → edge m e f g u v=true) :
    ∃ a b : V,∃ p : G.Walk a b,p.IsPath ∧ ∀ v,v∈p.support := by
  have bounds (k : Fin 12) (kk : k∈({0,1,9,10}:Finset (Fin 12))) :
      (d2Set m e f g k).card≤4 := by
    let Q := d2Set m e f g k
    have sub : Q.image φ⊆DistanceTwo G (φ k) := by
      intro y hy
      obtain ⟨v,vq,rfl⟩ := mem_image.mp hy
      obtain ⟨vne,no,w,kw,wv⟩ := (mem_filter.mp vq).2
      have ne : φ k≠φ v := fun e => vne (injection e).symm
      have no' : ¬G.Adj (φ k) (φ v) := by
        intro h
        have e := centers k kk v h
        simp [e] at no
      have low := hc.one_lt_dist_of_ne_of_not_adj ne no'
      have high := G.dist_le (Walk.cons (edges k w kw) (Walk.cons (edges w v wv) Walk.nil))
      simp at high
      simp [DistanceTwo, show G.dist (φ k) (φ v)=2 by omega]
    have c := card_le_card sub
    rw [card_image_of_injective _ injection] at c
    exact c.trans (cap _)
  have z := tiny m e f g left sf tg (bounds 0 (by decide)) (bounds 10 (by decide))
    (bounds 1 (by decide)) (bounds 9 (by decide))
  obtain ⟨mm,ee,ff,gg⟩ := z
  have eq : m=lastThree := funext mm
  let L : List (Fin 12) := [0,8,1,11,9,2,10,3,4,5,6,7]
  have chain : List.Chain' (fun u v => edge lastThree true true true u v=true) L := by decide
  have lchain : List.Chain' G.Adj (L.map φ) := List.chain'_map_of_chain' φ (by
    intro i j h
    apply edges i j
    simpa only [eq,ee,ff,gg] using h) chain
  have hn : L.Nodup := by decide
  have lnd : (L.map φ).Nodup := hn.map injection
  have mem (v : V) : v∈L.map φ := by
    obtain ⟨k,rfl⟩ := onto v
    refine List.mem_map.mpr ⟨k,?_,rfl⟩
    fin_cases k <;> decide
  let T : List V := (L.map φ).tail
  have lt : L.map φ = φ 0 :: T := rfl
  obtain ⟨q,w,ws⟩ := construct_walk (φ 0) T (lt ▸ lchain)
  have we : w.support=L.map φ := ws.trans lt.symm
  exact ⟨φ 0,q,w,IsPath.mk' (we.symm ▸ lnd),fun v => we.symm ▸ mem v⟩
end Lift

#print axioms lift

end FourOrder12
