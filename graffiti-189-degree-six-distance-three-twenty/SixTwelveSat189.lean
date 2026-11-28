import SixSevenCosts189
import GraphSat189
import Mathlib.Logic.Equiv.Fin.Basic

namespace Graffiti189LongestPath.SixTwelveSat
open Finset SimpleGraph
open Graffiti189LongestPath.CrossSaturation.ThresholdSix (allowedRoles)
open private Graffiti189LongestPath.GraphSat.sat_of_true_literal
  Graffiti189LongestPath.GraphSat.all_false_of_not_sat from GraphSat189
set_option maxHeartbeats 20000000

abbrev V := Fin 12
structure Profile where
  p : ℕ
  q : ℕ
  role : V → Fin 8
  low : Option V

def color (r : Fin 8) (b : Bool) : Prop :=
  if b then r=2 ∨ r=3 else r=0 ∨ r=1

def seen (r : Fin 8) (b : Bool) : Prop :=
  if b then r=1 ∨ r=5 ∨ r=6 else r=3 ∨ r=4 ∨ r=6

instance (r : Fin 8) (b : Bool) : Decidable (color r b) := by
  unfold color; infer_instance

instance (r : Fin 8) (b : Bool) : Decidable (seen r b) := by
  unfold seen; infer_instance

def external (P : Profile) (i : V) : ℕ :=
  let r := P.role i
  match r.val with
  | 0=>P.p
  | 1=>P.p+1
  | 2=>P.q
  | 3=>P.q+1
  | 4=>P.q+1+(6-(P.p+P.q))
  | 5=>P.p+1+(6-(P.p+P.q))
  | _=>2+(6-(P.p+P.q))

def floor (P : Profile) (i : V) : ℕ :=
  (if P.low=some i then 2 else 6)-(if (P.role i).val<4 then 1 else 0)

structure Model (P : Profile) (G : SimpleGraph V) [DecidableRel G.Adj] (Near : V → V → Prop) where
  symm : ∀ i j, Near i j → Near j i
  compat : ∀ i j, G.Adj i j → P.role j∈allowedRoles (P.role i)
  visible : ∀ i b, seen (P.role i) b → ∃ j, color (P.role j) b ∧ G.Adj i j
  lower : ∀ i j k, i≠j → G.Adj i k → G.Adj k j → ¬G.Adj i j → Near i j
  same : ∀ i j b, i≠j → color (P.role i) b → color (P.role j) b → ¬G.Adj i j → Near i j
  degree : ∀ i,floor P i≤G.degree i
  cap : ∀ i (s : Finset V), (∀ j∈s,Near i j) → s.card+external P i≤6

abbrev Atom := (Fin 2 × V) × V
def atomEquiv : Atom ≃ Fin (2*12*12) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl V)).trans finProdFinEquiv
def pack (a : Atom) : ℕ := (atomEquiv a).val
def symCode (g : Fin 2) (i j : V) : ℕ :=
  if i.val≤j.val then pack ((g,i),j) else pack ((g,j),i)
def edge (i j : V) := symCode 0 i j
def near (i j : V) := symCode 1 i j

private def semantic (G : SimpleGraph V) (Near : V → V → Prop) (a : Atom) : Prop :=
  if a.1.1=0 then G.Adj a.1.2 a.2 else Near a.1.2 a.2

private def valuation (G : SimpleGraph V) (Near : V → V → Prop) : Sat.Valuation :=
  fun n=>∃ a : Atom,pack a=n ∧ semantic G Near a

private theorem val_pack {G : SimpleGraph V} {Near : V → V → Prop} (a : Atom) :
    valuation G Near (pack a) ↔ semantic G Near a := by
  constructor
  · rintro ⟨b,h,e⟩
    exact (atomEquiv.injective (Fin.ext h)) ▸ e
  · exact fun h=>⟨a,rfl,h⟩

private theorem val_edge {G : SimpleGraph V} {Near : V → V → Prop} (i j : V) :
    valuation G Near (edge i j) ↔ G.Adj i j := by
  unfold edge symCode
  split
  · rw [val_pack]; rfl
  · rw [val_pack]
    exact ⟨fun h=>SimpleGraph.Adj.symm h,fun h=>h.symm⟩

private theorem val_near {G : SimpleGraph V} {Near : V → V → Prop}
    (symm : ∀ i j,Near i j → Near j i) (i j : V) :
    valuation G Near (near i j) ↔ Near i j := by
  unfold near symCode
  split
  · rw [val_pack]; rfl
  · rw [val_pack]
    exact ⟨symm j i,symm i j⟩

inductive Rule where
  | forbidden (i j : V)
  | visible (i : V) (b : Bool)
  | lower (i j k : V)
  | same (i j : V) (b : Bool)
  | degree (i : V) (keep : List V)
  | cap (i : V) (xs : List V)

def Rule.clause (P : Profile) : Rule→List Sat.Literal
  | .forbidden i j=>[.neg (edge i j)]
  | .visible i b=>((List.finRange 12).filter (fun j=>decide (color (P.role j) b))).map (fun j=>.pos (edge i j))
  | .lower i j k=>[.neg (edge i k),.neg (edge k j),.pos (edge i j),.pos (near i j)]
  | .same i j _=>[.pos (edge i j),.pos (near i j)]
  | .degree i keep=>((List.finRange 12).filter (fun j=>decide (j≠i ∧ j∉keep ∧ P.role j∈allowedRoles (P.role i)))).map (fun j=>.pos (edge i j))
  | .cap i xs=>xs.map fun j=>.neg (near i j)

def Rule.WF (P : Profile) : Rule→Prop
  | .forbidden i j=>P.role j∉allowedRoles (P.role i)
  | .visible i b=>seen (P.role i) b
  | .lower i j _=>i≠j
  | .same i j b=>i≠j ∧ color (P.role i) b ∧ color (P.role j) b
  | .degree i keep=>keep.length<floor P i
  | .cap i xs=>xs.Nodup ∧ 6<xs.length+external P i

instance (P : Profile) (r : Rule) : Decidable (r.WF P) := by
  cases r <;> simp only [Rule.WF] <;> infer_instance

private theorem posSat (v : Sat.Valuation) (c : List Sat.Literal) (a : ℕ)
    (inC : .pos a∈c) (va : v a) : v.satisfies c :=
  Graffiti189LongestPath.GraphSat.sat_of_true_literal v c (.pos a) inC (fun h=>h va)

private theorem negSat (v : Sat.Valuation) (c : List Sat.Literal) (a : ℕ)
    (inC : .neg a∈c) (va : ¬v a) : v.satisfies c :=
  Graffiti189LongestPath.GraphSat.sat_of_true_literal v c (.neg a) inC va

theorem satisfies_rule {P : Profile} {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model P G Near) (r : Rule) (wr : r.WF P) :
    (valuation G Near).satisfies (r.clause P) := by
  classical
  let v := valuation G Near
  have e := val_edge (G:=G) (Near:=Near)
  have d := val_near (G:=G) M.symm
  change v.satisfies (r.clause P)
  cases r with
  | forbidden i j =>
    exact negSat v _ _ (by simp [Rule.clause]) (fun h => wr (M.compat _ _ ((e i j).mp h)))
  | visible i b =>
    obtain ⟨j,jc,ij⟩ := M.visible i b wr
    exact posSat v _ (edge i j) (by
      exact List.mem_map.mpr ⟨j,by simp [jc],rfl⟩) ((e i j).mpr ij)
  | lower i j k =>
    by_cases ik : G.Adj i k
    · by_cases kj : G.Adj k j
      · by_cases ij : G.Adj i j
        · exact posSat v _ (edge i j) (by simp [Rule.clause]) ((e i j).mpr ij)
        · exact posSat v _ (near i j) (by simp [Rule.clause]) ((d i j).mpr (M.lower i j k wr ik kj ij))
      · exact negSat v _ (edge k j) (by simp [Rule.clause]) (fun h=>kj ((e k j).mp h))
    · exact negSat v _ (edge i k) (by simp [Rule.clause]) (fun h=>ik ((e i k).mp h))
  | same i j b =>
    by_cases ij : G.Adj i j
    · exact posSat v _ (edge i j) (by simp [Rule.clause]) ((e i j).mpr ij)
    · exact posSat v _ (near i j) (by simp [Rule.clause]) ((d i j).mpr (M.same i j b wr.1 wr.2.1 wr.2.2 ij))
  | degree i keep =>
    have out : ∃ j,G.Adj i j ∧ j∉keep := by
      apply Classical.byContradiction
      intro no
      have sub : G.neighborFinset i ⊆ keep.toFinset := by
        intro j jj
        apply List.mem_toFinset.mpr
        by_contra jn
        exact no ⟨j,(G.mem_neighborFinset _ _).mp jj,jn⟩
      have c := card_le_card sub
      rw [G.card_neighborFinset_eq_degree] at c
      have k := List.toFinset_card_le keep
      have l := M.degree i
      change keep.length<floor P i at wr
      omega
    obtain ⟨j,ij,jk⟩ := out
    exact posSat v _ (edge i j) (List.mem_map.mpr ⟨j,by simp [ij.ne.symm,jk,M.compat _ _ ij],rfl⟩) ((e i j).mpr ij)
  | cap i xs =>
    apply Classical.byContradiction
    intro no
    have h : ∀ j∈xs.toFinset,Near i j := by
      intro j jm
      apply (d i j).mp
      exact Graffiti189LongestPath.GraphSat.all_false_of_not_sat v _ no _
        (List.mem_map.mpr ⟨j,List.mem_toFinset.mp jm,rfl⟩)
    have bd := M.cap i _ h
    rw [List.toFinset_card_of_nodup wr.1] at bd
    exact (Nat.not_lt_of_ge bd) wr.2

theorem transfer {P : Profile} {G : SimpleGraph V} [DecidableRel G.Adj] {Near : V → V → Prop}
    (M : Model P G Near) (rules : List Rule) (ok : ∀ r∈rules,r.WF P)
    (cert : Sat.Fmla.proof (rules.map (Rule.clause P)) []) : False := by
  apply cert (valuation G Near)
  constructor
  intro c cm
  obtain ⟨r,rm,rfl⟩ := List.mem_map.mp cm
  exact satisfies_rule M r (ok r rm)

#print axioms transfer
end Graffiti189LongestPath.SixTwelveSat
