import ModelFromGraph189

open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.GraphSat
open private Graffiti189LongestPath.GraphSat.valuation Graffiti189LongestPath.GraphSat.val_edge Graffiti189LongestPath.GraphSat.all_false_of_not_sat from GraphSat189
open private Graffiti189LongestPath.GraphSat.walk_of_chain
  Graffiti189LongestPath.GraphSat.chain_of_pathEdges from ModelFromGraph189

namespace Graffiti189LongestPath.MarkedWingSat

inductive Rule (n : ℕ) where
  | degree (i : Fin n) (forbid : List (Fin n))
  | route (p : List (Fin n))

def clause {n : ℕ} : Rule n → Sat.Clause
  | .degree i xs => ((List.finRange n).filter (fun j => j≠i ∧ j∉xs)).map
      (fun j => .pos (edgeId i j))
  | .route p => (pathEdges p).map (fun (i,j) => .neg (edgeId i j))

def WF {n : ℕ} (z s t : Fin n) : Rule n→Prop
  | .degree i xs => xs.length < (if i=z then 2 else 4)
  | .route p => p.Nodup ∧ 5≤p.length ∧ p.head?=some s ∧ p.getLast?=some t

instance {n : ℕ} (z s t : Fin n) (r : Rule n) : Decidable (WF z s t r) := by
  cases r <;> simp only [WF] <;> infer_instance

private theorem has_start_end {n : ℕ} {D : SimpleGraph (Fin n)}
    {s t : Fin n} (p : List (Fin n)) (wf : WF s s t (.route p))
    (edges : ∀ i j, (i,j)∈pathEdges p → D.Adj i j) :
    ∃ q : D.Walk s t,q.IsPath ∧ 4≤q.length := by
  have c := Graffiti189LongestPath.GraphSat.chain_of_pathEdges (G:=D) id p edges
  simp only [List.map_id_fun] at c
  rcases wf with ⟨nd,len,front,last⟩
  cases p with
  | nil => simp at front
  | cons st tail =>
    have st_eq : st=s := Option.some.inj front
    subst st
    obtain ⟨b,q,sup⟩ := Graffiti189LongestPath.GraphSat.walk_of_chain (G:=D) s tail c
    have z : q.support.getLast?=some b := by
      rw [List.getLast?_eq_getLast (by simp),q.getLast_support]
    have e : b=t := Option.some.inj (z.symm.trans (sup ▸ last))
    subst b
    have ql := q.length_support
    rw [sup] at ql
    exact ⟨q,(isPath_def q).mpr (sup.symm ▸ nd),by omega⟩

theorem transfer {n : ℕ} (pos : 0<n) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (z s t : Fin n) (degrees : ∀ i, (if i=z then 2 else 4)≤G.degree i)
    (rules : List (Rule n)) (ok : ∀ r∈rules,WF z s t r)
    (cnf : Sat.Fmla.proof (rules.map clause) []) :
    ∃ p : G.Walk s t,p.IsPath ∧ 4≤p.length := by
  classical
  apply Classical.byContradiction
  intro no
  let v := Graffiti189LongestPath.GraphSat.valuation pos G.Adj (fun _ _ => False)
  have val (i j : Fin n) :
      v (edgeId i j) ↔ G.Adj i j :=
    Graffiti189LongestPath.GraphSat.val_edge pos G.Adj _ G.symm i j
  apply cnf v
  constructor
  intro C hC
  obtain ⟨rule,rm,rfl⟩ := List.mem_map.mp hC
  have h := ok _ rm
  cases rule with
  | degree i xs =>
    have out : ∃ j,G.Adj i j ∧ j∉xs := by
      apply Classical.byContradiction
      intro no
      have sub : G.neighborFinset i ⊆ xs.toFinset := by
        intro j jj
        apply List.mem_toFinset.mpr
        exact Classical.byContradiction (fun jn => no ⟨j,(G.mem_neighborFinset _ _).mp jj,jn⟩)
      have c := card_le_card sub
      rw [G.card_neighborFinset_eq_degree] at c
      have dl := List.toFinset_card_le xs
      have di := degrees i
      change xs.length < (if i=z then 2 else 4) at h
      omega
    obtain ⟨j,ij,jx⟩ := out
    have mem : List.Mem (.pos (edgeId i j)) (clause (.degree i xs)) := by
      exact List.mem_map.mpr ⟨j,by simp [ij.ne.symm,jx],rfl⟩
    apply Classical.byContradiction
    intro nC
    have hFalse := Graffiti189LongestPath.GraphSat.all_false_of_not_sat v _ nC _ mem
    exact (show ¬v (edgeId i j) from hFalse) ((val i j).mpr ij)
  | route p =>
    apply Classical.byContradiction
    intro nC
    apply no
    apply has_start_end p h
    intro i j ij
    apply (val i j).mp
    exact Graffiti189LongestPath.GraphSat.all_false_of_not_sat v _ nC _
      (List.mem_map.mpr ⟨(i,j),ij,rfl⟩)

#print axioms transfer
end Graffiti189LongestPath.MarkedWingSat
