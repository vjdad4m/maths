import Equality24ProfileMiddle189
import GraphSat189
import Mathlib.Logic.Equiv.Fin.Basic

open Finset SimpleGraph Graffiti189LongestPath
open Graffiti189LongestPath.Equality24Profile Graffiti189LongestPath.Layer24Numbering
open private Graffiti189LongestPath.GraphSat.sat_of_true_literal
  Graffiti189LongestPath.GraphSat.all_false_of_not_sat from GraphSat189

set_option linter.unusedSectionVars false
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

namespace Graffiti189LongestPath.Equality24CNF

abbrev Atom := (((Fin 6 × Vert) × Vert) × Vert)
def atomEquiv : Atom ≃ Fin (6*24*24*24) :=
  ((Equiv.prodCongr (Equiv.prodCongr finProdFinEquiv (Equiv.refl Vert))
    (Equiv.refl Vert)).trans
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl Vert))).trans finProdFinEquiv

def pack (a : Atom) : ℕ := (atomEquiv a).val

def symCode (g : Fin 6) (i j k : Vert) : ℕ :=
  if i.val≤j.val then pack (((g,i),j),k) else pack (((g,j),i),k)

def edge (i j : Vert) := symCode 0 i j 0
def near (i j : Vert) := symCode 1 i j 0
def via (i j k : Vert) := symCode 2 i j k
def high (i : Vert) := pack (((3,i),0),0)

def sample (G : SimpleGraph Vert) (d : Bool) (i j : Vert) : Prop :=
  if d then TwoStep G i j else G.Adj i j

instance sampleDecidable (G : SimpleGraph Vert) [DecidableRel G.Adj] (d : Bool) :
    DecidableRel (sample G d) := fun i j => by
  cases d <;> simp only [sample] <;> infer_instance

def vertexSlice (G : SimpleGraph Vert) [DecidableRel G.Adj] (d : Bool) (i p : Vert) : Finset Vert :=
  univ.filter fun j => j.val≤p.val ∧ sample G d i j

def countCode (d : Bool) (i p k : Vert) :=
  pack (((if d then 5 else 4,i),p),k)

def semantic (G : SimpleGraph Vert) [DecidableRel G.Adj] (a : Atom) : Prop :=
  let (((t,i),j),k) := a
  if t=0 then G.Adj i j
  else if t=1 then TwoStep G i j
  else if t=2 then G.Adj i k ∧ G.Adj k j
  else if t=3 then 6≤G.degree i
  else k.val≤(vertexSlice G (decide (t=5)) i j).card

private def valuation (G : SimpleGraph Vert) [DecidableRel G.Adj] : Sat.Valuation :=
  fun n => ∃ a : Atom, pack a=n ∧ semantic G a

private theorem val_pack {G : SimpleGraph Vert} [DecidableRel G.Adj] (a : Atom) :
    valuation G (pack a) ↔ semantic G a := by
  constructor
  · rintro ⟨b,h,e⟩
    have eq := atomEquiv.injective (Fin.ext h)
    exact eq ▸ e
  · exact fun h => ⟨a,rfl,h⟩

private theorem val_edge {G : SimpleGraph Vert} [DecidableRel G.Adj] (i j : Vert) :
    valuation G (edge i j) ↔ G.Adj i j := by
  unfold edge symCode
  by_cases e : i.val≤j.val
  · rw [if_pos e,val_pack]
    rfl
  · rw [if_neg e,val_pack]
    exact ⟨fun h => SimpleGraph.Adj.symm h,fun h => h.symm⟩

private theorem val_near {G : SimpleGraph Vert} [DecidableRel G.Adj] (i j : Vert) :
    valuation G (near i j) ↔ TwoStep G i j := by
  unfold near symCode
  by_cases e : i.val≤j.val
  · rw [if_pos e,val_pack]
    rfl
  · rw [if_neg e,val_pack]
    exact twoStep_symm

private theorem val_via {G : SimpleGraph Vert} [DecidableRel G.Adj] (i j k : Vert) :
    valuation G (via i j k) ↔ (G.Adj i k ∧ G.Adj k j) := by
  unfold via symCode
  by_cases e : i.val≤j.val
  · rw [if_pos e,val_pack]
    rfl
  · rw [if_neg e,val_pack]
    change (G.Adj j k ∧ G.Adj k i) ↔ _
    exact ⟨fun h => ⟨h.2.symm,h.1.symm⟩,fun h => ⟨h.2.symm,h.1.symm⟩⟩

private theorem val_high {G : SimpleGraph Vert} [DecidableRel G.Adj] (i : Vert) :
    valuation G (high i) ↔ 6≤G.degree i := by
  rw [high,val_pack]
  rfl

inductive Rule where
  | loop (i : Vert)
  | selfNear (i : Vert)
  | parent (i : Vert) (ps : List Vert)
  | fixedEdge (i j : Vert) (q : Bool)
  | fixedNear (i j : Vert) (q : Bool)
  | cross (i j : Vert)
  | existsVia (i j : Vert)
  | nearNonedge (i j : Vert)
  | viaLeft (i j k : Vert)
  | viaRight (i j k : Vert)
  | highPair (i j : Vert)
  | lower (i k j : Vert)
  | cap (i : Vert) (nearby : List Vert)
  | highOutside (i : Vert) (forbidden : List Vert)

def literal (q : Bool) (m : Nat) : Sat.Literal := if q then .pos m else .neg m

def Rule.clause : Rule → List Sat.Literal
  | .loop i => [.neg (edge i i)]
  | .selfNear i => [.neg (near i i)]
  | .parent i ps => ps.map (fun j=>.pos (edge i j))
  | .fixedEdge i j q => [literal q (edge i j)]
  | .fixedNear i j q => [literal q (near i j)]
  | .cross i j => [.neg (near i (markedOf j)),.pos (edge i j)]
  | .existsVia i j => .neg (near i j) :: (List.finRange 24).map (fun k => .pos (via i j k))
  | .nearNonedge i j => [.neg (near i j),.neg (edge i j)]
  | .viaLeft i j k => [.neg (via i j k),.pos (edge i k)]
  | .viaRight i j k => [.neg (via i j k),.pos (edge k j)]
  | .highPair i j => [.pos (high i),.pos (high j)]
  | .lower i k j => [.neg (edge i k),.neg (edge k j),.pos (edge i j),.pos (near i j)]
  | .cap i xs => xs.map (fun j => .neg (near i j))
  | .highOutside i xs => .neg (high i) ::
     ((List.finRange 24).filter (fun j => j≠i ∧ j∉xs)).map (fun j => .pos (edge i j))

def Rule.WF (m : Kind) (t b : Nat) : Rule → Prop
  | .fixedEdge i j q => forcedAdj m t b i j=some q
  | .fixedNear i j q => forcedD2 m t b i j=some q
  | .cross i j => selected t i ∧ selected t j ∧ i≠j ∧ fullSelector m t (i.val-1)
  | .highPair i j => i≠j
  | .parent i ps => i≠0 ∧ ∀ j : Vert,layer m b j+1=layer m b i → j∈ps
  | .lower i _ j => i≠j
  | .cap _ xs => xs.Nodup ∧ xs.length=7
  | .highOutside _ xs => xs.length≤5
  | _ => True

instance (m : Kind) (t b : ℕ) (r : Rule) : Decidable (r.WF m t b) := by
  cases r <;> simp only [Rule.WF] <;> infer_instance

private theorem posSat (v : Sat.Valuation) (c : List Sat.Literal) (a : ℕ)
    (inC : .pos a∈c) (va : v a) : v.satisfies c :=
  Graffiti189LongestPath.GraphSat.sat_of_true_literal v c (.pos a) inC (fun h => h va)

private theorem negSat (v : Sat.Valuation) (c : List Sat.Literal) (a : ℕ)
    (inC : .neg a∈c) (va : ¬v a) : v.satisfies c :=
  Graffiti189LongestPath.GraphSat.sat_of_true_literal v c (.neg a) inC va

theorem satisfies_rule {G : SimpleGraph Vert} [DecidableRel G.Adj] {m : Kind} {t b : ℕ}
    (M : Model G m t b) (r : Rule) (wr : r.WF m t b) :
    (valuation G).satisfies r.clause := by
  classical
  let v := valuation G
  have ea := val_edge (G:=G)
  have na := val_near (G:=G)
  have va := val_via (G:=G)
  have ha := val_high (G:=G)
  change v.satisfies r.clause
  cases r with
  | loop i =>
    exact negSat v _ _ (by simp [Rule.clause]) (fun h => G.irrefl ((ea i i).mp h))
  | selfNear i =>
    exact negSat v _ _ (by simp [Rule.clause]) (fun h=>((na i i).mp h).1 rfl)
  | parent i ps =>
    obtain ⟨j,jdep,ij⟩ := M.parent i wr.1
    apply posSat v _ (edge i j) ?_ ((ea i j).mpr ij)
    exact List.mem_map.mpr ⟨j,wr.2 j jdep,rfl⟩
  | fixedEdge i j q =>
    have p := M.forcedEdge _ _ _ wr
    cases q
    · exact negSat v _ _ (by simp [Rule.clause,literal]) (fun h => Bool.noConfusion (p.mp ((ea i j).mp h)))
    · exact posSat v _ _ (by simp [Rule.clause,literal]) ((ea i j).mpr (p.mpr rfl))
  | fixedNear i j q =>
    have p := M.forcedShadow _ _ _ wr
    cases q
    · exact negSat v _ _ (by simp [Rule.clause,literal]) (fun h => Bool.noConfusion (p.mp ((na i j).mp h)))
    · exact posSat v _ _ (by simp [Rule.clause,literal]) ((na i j).mpr (p.mpr rfl))
  | cross i j =>
    by_cases h : TwoStep G i (markedOf j)
    · exact posSat v _ _ (by simp [Rule.clause]) ((ea i j).mpr (M.cross _ _ wr.1 wr.2.1 wr.2.2.1 wr.2.2.2 h))
    · exact negSat v _ _ (by simp [Rule.clause]) (fun e => h ((na i (markedOf j)).mp e))
  | existsVia i j =>
    by_cases h : TwoStep G i j
    · obtain ⟨k,ka,kb⟩ := h.2.2
      apply posSat v _ (via i j k) ?_ ((va i j k).mpr ⟨ka,kb⟩)
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k,by simp,rfl⟩)
    · exact negSat v _ _ (by simp [Rule.clause]) (fun e => h ((na i j).mp e))
  | nearNonedge i j =>
    by_cases h : TwoStep G i j
    · exact negSat v _ (edge i j) (by simp [Rule.clause]) (fun e => h.2.1 ((ea i j).mp e))
    · exact negSat v _ _ (by simp [Rule.clause]) (fun e => h ((na i j).mp e))
  | viaLeft i j k =>
    by_cases h : G.Adj i k
    · exact posSat v _ _ (by simp [Rule.clause]) ((ea i k).mpr h)
    · exact negSat v _ _ (by simp [Rule.clause]) (fun e => h ((va i j k).mp e).1)
  | viaRight i j k =>
    by_cases h : G.Adj k j
    · exact posSat v _ _ (by simp [Rule.clause]) ((ea k j).mpr h)
    · exact negSat v _ _ (by simp [Rule.clause]) (fun e => h ((va i j k).mp e).2)
  | highPair i j =>
    rcases M.pair _ _ wr with ih|jh
    · exact posSat v _ (high i) (by simp [Rule.clause]) ((ha i).mpr ih)
    · exact posSat v _ (high j) (by simp [Rule.clause]) ((ha j).mpr jh)
  | lower i k j =>
    by_cases ki : G.Adj i k
    · by_cases kj : G.Adj k j
      · by_cases ij : G.Adj i j
        · exact posSat v _ (edge i j) (by simp [Rule.clause]) ((ea i j).mpr ij)
        · exact posSat v _ (near i j) (by simp [Rule.clause]) ((na i j).mpr ⟨wr,ij,k,ki,kj⟩)
      · exact negSat v _ (edge k j) (by simp [Rule.clause]) (fun e => kj ((ea k j).mp e))
    · exact negSat v _ (edge i k) (by simp [Rule.clause]) (fun e => ki ((ea i k).mp e))
  | cap i xs =>
    by_contra no
    have sub : xs.toFinset⊆Shadow G i := by
      intro j jj
      have mem : Sat.Literal.neg (near i j)∈(Rule.cap i xs).clause :=
        List.mem_map.mpr ⟨j,List.mem_toFinset.mp jj,rfl⟩
      have h := Graffiti189LongestPath.GraphSat.all_false_of_not_sat v _ no _ mem
      exact mem_filter.mpr ⟨mem_univ _,(na i j).mp h⟩
    have h := (card_le_card sub).trans (M.cap _)
    rw [List.toFinset_card_of_nodup wr.1,wr.2] at h
    omega
  | highOutside i xs =>
    by_cases di : 6≤G.degree i
    · have out : ∃ j,G.Adj i j ∧ j∉xs := by
        apply Classical.byContradiction
        intro no
        have sub : G.neighborFinset i⊆xs.toFinset := by
          intro j jj
          exact List.mem_toFinset.mpr (Classical.byContradiction
            (fun jn => no ⟨j,(G.mem_neighborFinset _ _).mp jj,jn⟩))
        have h := (card_le_card sub).trans (List.toFinset_card_le xs)
        rw [G.card_neighborFinset_eq_degree] at h
        change xs.length≤5 at wr
        omega
      obtain ⟨j,ij,jx⟩ := out
      apply posSat v _ (edge i j) ?_ ((ea i j).mpr ij)
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,by simp [ij.ne.symm,jx],rfl⟩)
    · exact negSat v _ _ (by simp [Rule.clause]) (fun e => di ((ha i).mp e))

theorem contradiction_of_proof {G : SimpleGraph Vert} [DecidableRel G.Adj] {m : Kind} {t b : ℕ}
    (M : Model G m t b) (rules : List Rule) (wf : ∀ r∈rules,r.WF m t b)
    (certificate : Sat.Fmla.proof (rules.map Rule.clause) []) : False := by
  apply certificate (valuation G)
  constructor
  intro C hC
  obtain ⟨r,rm,rfl⟩ := List.mem_map.mp hC
  exact satisfies_rule M r (wf _ rm)

#print axioms contradiction_of_proof
end Graffiti189LongestPath.Equality24CNF
