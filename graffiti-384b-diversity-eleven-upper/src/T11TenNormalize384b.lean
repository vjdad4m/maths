import T11TenCut384b
import T11TenRelabel384b

namespace Graffiti384b.T11TenNormalize
open Finset SimpleGraph
set_option maxHeartbeats 3000000

private theorem pull_filtered_neighbor_count (G : SimpleGraph Label) [DecidableRel G.Adj]
    (A : Finset Label) (p : Label ≃ Label) (r : Label) (S : Finset Label)
    (fits : ∀ i, G.Adj (p r) (p i) ↔ i∈S) :
    ((S.filter (opposite (A.map p.symm.toEmbedding) r)).card) =
      ((G.neighborFinset (p r)).filter (opposite A (p r))).card := by
  have eq : (S.filter (opposite (A.map p.symm.toEmbedding) r)).map p.toEmbedding =
      (G.neighborFinset (p r)).filter (opposite A (p r)) := by
    ext v
    obtain ⟨i,rfl⟩ := p.surjective v
    have mapped := Finset.mem_map' p.toEmbedding (a:=i)
      (s:=S.filter (opposite (A.map p.symm.toEmbedding) r))
    change p i ∈ _ ↔ i∈_ at mapped
    rw [mapped,Finset.mem_filter,Finset.mem_filter,G.mem_neighborFinset,fits]
    simp [opposite]
  rw [←eq,Finset.card_map]

/-- Exact normalization of two nonadjacent cubic vertices with scores two
and three, together with a balanced cut splitting both cubic neighborhoods. -/
theorem normalize (G : SimpleGraph Label) [DecidableRel G.Adj]
    (u v : Label) (uv : u≠v) (sep : ¬G.Adj u v)
    (du : G.degree u=3) (su : trianglesAt G u=2) (dv : G.degree v=3) (sv : trianglesAt G v=3)
    (A : Finset Label) (size : A.card=5) (vA : v∈A)
    (uOpp : ((G.neighborFinset u).filter (opposite A u)).card=2)
    (vOpp : ((G.neighborFinset v).filter (opposite A v)).card=2) :
    ∃ (k : Fin 4) (p : Label ≃ Label) (m : Nat),
      p 0=v ∧ p 4=u ∧ m∈allowedCuts k ∧
      (∀ i : Label, p i∈A ↔ m.testBit i.val=true) ∧
      (∀ i j b, motif k i j=some b → (G.Adj (p i) (p j) ↔ b=true)) := by
  obtain ⟨k,p,pv,pu,cp,dp,fits⟩ := normalize_motif G u v uv sep du su dv sv
  let B := A.map p.symm.toEmbedding
  have mem (i : Label) : i∈B ↔ p i∈A := by simp [B]
  have c : B.card=5 := by simp [B,size]
  have b0 : (0:Label)∈B := (mem 0).mpr (pv.symm ▸ vA)
  have cv : ((clique.filter (opposite B 0)).card)=2 := by
    have eq := pull_filtered_neighbor_count G A p 0 clique (fun i => by rw [pv]; exact cp i)
    rw [pv,vOpp] at eq
    exact eq
  have cu : (((diamond k).filter (opposite B 4)).card)=2 := by
    have eq := pull_filtered_neighbor_count G A p 4 (diamond k) (fun i => by rw [pu]; exact dp i)
    rw [pu,uOpp] at eq
    exact eq
  obtain ⟨e,m,e0,e4,mc,colors,h⟩ := normalize_cut k B c b0 cv cu
  let q := e.trans p
  refine ⟨k,q,m,?_,?_,mc,?_,?_⟩
  · change p (e 0)=v; rw [e0,pv]
  · change p (e 4)=u; rw [e4,pu]
  · intro i; exact (mem (e i)).symm.trans (colors i)
  · intro i j b hab
    exact fits (e i) (e j) b ((h i j).symm.trans hab)

end Graffiti384b.T11TenNormalize
#print axioms Graffiti384b.T11TenNormalize.normalize
