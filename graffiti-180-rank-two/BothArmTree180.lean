import TreeOrientation180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Root a reference parity tree at the attachment t. Tightness implies
that the predecessor of every other disagreement stays in the disagreement
set. The exchange keeps both original root edges and an eligible terminal. -/
theorem both_arm_tree {G : SimpleGraph V} {r t w a b : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    t∈D → w∉D → G.Adj t w → a∉D → b∉D → a≠w → G.Adj a b →
    ∃ T≤G, T.IsTree ∧ r∉leaves T ∧ T.Adj a b ∧ (∃ v∈D,v∈leaves T) ∧
      ∃ p : V→V, ∃ d : V→ℕ, ∀ i∈D,T.Adj i (p i) ∧ (p i∈D ∨ p i=w) ∧ d (p i)<d i := by
  classical
  intro P D td wd tw ad bd aw ab
  let H := alternating G P
  obtain ⟨hc,star⟩ := alternating_parity G h.connected r odd
  obtain ⟨F,fh,ft⟩ := hc.exists_isTree_le
  obtain ⟨M,mh,mt,full,_⟩ := full_star_exchange H F fh ft (by have := h.order; omega) r
  have mg : M≤G := fun _ _ e => (mh e).1
  obtain ⟨i,j,ri,rj,ij⟩ := block_neighbors G h.connected h.order h.block r
  have ei := full i (star i ri)
  have ej := full j (star j rj)
  have im : i∈D := both_ports h ri
  have jm : j∈D := both_ports h rj
  have rd : r∈D := h.root_disagreement
  have root : r∉leaves M := fun l => ij (leaf_unique M l ei ej)
  have count := (h.rigid M mt mg root fun e => (mh e).2).2
  change (M.edgeFinset∩D.sym2).card+1=D.card at count
  obtain ⟨q,arc,edges⟩ := orient_tree M mt t
  rw [chosen_parent_count M mt t D q (fun z => M.dist z t)
    (fun z zt => (arc z zt).2.1) (fun z zt => (arc z zt).1.symm)] at count
  have size := card_erase_add_one td
  have eq := eq_of_subset_of_card_le (filter_subset (fun z => q z∈D) (D.erase t)) (by omega)
  have prior (z : V) (zd : z∈D) (zt : z≠t) : ∃ p∈D,Arc M t p z := by
    have inc : z∈(D.erase t).filter (fun v => q v∈D) := by rw [eq]; exact mem_erase.mpr ⟨zt,zd⟩
    exact ⟨q z,(mem_filter.mp inc).2,arc z zt⟩
  obtain ⟨v,vd,last⟩ := exists_max_image D (fun z => M.dist z t) ⟨t,td⟩
  have vt : v≠t := by
    intro e
    have li := last i im
    have lj := last j jm
    rw [e,dist_self] at li lj
    exact ij ((mt.isConnected.dist_eq_zero_iff.mp (by omega : M.dist i t=0)).trans
      (mt.isConnected.dist_eq_zero_iff.mp (by omega : M.dist j t=0)).symm)
  obtain ⟨T,tg,tree,_,keep,eab,⟨k,kd,_,kl⟩,p,d,down⟩ := arm_tree_in mg h.block
    (by have := h.order; omega) td prior vd vt last wd tw ad bd aw ab
  have fixed {c e : V} (cd : c∈D) (ed : e∈D) (ce : M.Adj c e) : T.Adj c e := by
    rcases edges c e ce with ⟨ct,qc⟩|⟨et,qe⟩
    · exact qc ▸ keep c cd ct (q c) (arc c ct)
    · exact qe ▸ (keep e ed et (q e) (arc e et)).symm
  exact ⟨T,tg,tree,(fun lf => ij (leaf_unique T lf (fixed rd im ei) (fixed rd jm ej))),
    eab,⟨k,kd,kl⟩,p,d,down⟩

#print axioms both_arm_tree
end Minimal180.RootEar
