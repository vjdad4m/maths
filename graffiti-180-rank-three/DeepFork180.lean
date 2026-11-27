import ForkTree180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pred_vertical (G : SimpleGraph V) (r : V) (odd : Bool) {x y : V}
    (pr : Pred G r x y) : (alternating G (parity G r odd)).Adj x y := by
  refine ⟨pr.1,?_⟩
  simp only [mem_parity,pr.2]
  cases odd <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

/-- In a failed deficit-three marking, two deep marked forks with distinct
successor pairs meeting in m necessarily have the same unique predecessor.
This conclusion uses a tree allowed to change the distances to the root. -/
theorem deep_fork_parents (G : SimpleGraph V) (hc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (two : ∃ s t,G.Adj r s ∧ G.Adj r t ∧ s≠t) (odd : Bool)
    (A : Finset V) (ai : Indep G A) (rk : Fintype.card V≤bipartiteNum G+3)
    (u v m a b y z : V) (uv : u≠v) (am : a≠m) (bm : b≠m) (ab : a≠b)
    (mu : Pred G r m u) (mv : Pred G r m v) (au : Pred G r a u) (bv : Pred G r b v)
    (uy : Pred G r u y) (vz : Pred G r v z) (deep : 3≤G.dist u r) :
    let P := parity G r odd
    u∈A∪P → v∈A∪P →
    weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card → y=z := by
  classical
  intro P um vm bad
  by_contra yz
  let H := alternating G P
  let C : Finset V := {u,v}
  let L : Finset V := {a,b,y,z}
  let f (x : V) := if x=a ∨ x=y then u else v
  obtain ⟨s,t,rs,rt,st⟩ := two
  have dm := mu.2
  have dv := mv.2
  have da := au.2
  have db := bv.2
  have dy := uy.2
  have dz := vz.2
  have dr : G.dist r r=0 := dist_self
  have ds := dist_eq_one_iff_adj.mpr rs.symm
  have dt := dist_eq_one_iff_adj.mpr rt.symm
  have lc (x : V) (xc : x∈C) : G.dist x r=G.dist u r := by
    rcases (show x=u ∨ x=v by simpa [C] using xc) with eq|eq <;> subst x <;> omega
  have ll (x : V) (xl : x∈L) : G.dist x r=G.dist u r+1 ∨ G.dist x r+1=G.dist u r := by
    rcases (show x=a ∨ x=b ∨ x=y ∨ x=z by simpa [L] using xl) with eq|eq|eq|eq <;> subst x <;> omega
  have dis : Disjoint C L := disjoint_left.mpr fun x xc xl => by
    have := lc x xc; have := ll x xl; omega
  have low (x : V) (d : G.dist x r≤1) : x∉C∪L := by
    intro h
    rcases mem_union.mp h with xc|xl
    · have := lc x xc; omega
    · have := ll x xl; omega
  have my : m≠y := by intro eq; rw [eq] at dm; omega
  have mz : m≠z := by intro eq; rw [eq] at dv; omega
  have fm : m∉C∪L := by
    intro h
    rcases mem_union.mp h with xc|xl
    · have := lc m xc; omega
    · simp [L,am.symm,bm.symm,my,mz] at xl
  have free : ∀ x∈({r,m,s,t}:Finset V),x∉C∪L := by
    intro x hx
    rcases (show x=r ∨ x=m ∨ x=s ∨ x=t by simpa using hx) with eq|eq|eq|eq <;> subst x
    · exact low r (by omega)
    · exact fm
    · exact low s (by omega)
    · exact low t (by omega)
  have byn : b≠y := by intro eq; rw [eq] at db; omega
  have zan : z≠a := by intro eq; rw [eq] at dz; omega
  have fa : f a=u := by simp [f]
  have fy : f y=u := by simp [f]
  have fb : f b=v := by simp [f,ab.symm,byn]
  have fz : f z=v := by simp [f,zan,Ne.symm yz]
  have eu := pred_vertical G r odd mu
  have ev := pred_vertical G r odd mv
  have arm (x : V) (xl : x∈L) : f x∈C ∧ H.Adj x (f x) := by
    rcases (show x=a ∨ x=b ∨ x=y ∨ x=z by simpa [L] using xl) with eq|eq|eq|eq <;> subst x
    · rw [fa]; exact ⟨by simp [C],pred_vertical G r odd au⟩
    · rw [fb]; exact ⟨by simp [C],pred_vertical G r odd bv⟩
    · rw [fy]; exact ⟨by simp [C],(pred_vertical G r odd uy).symm⟩
    · rw [fz]; exact ⟨by simp [C],(pred_vertical G r odd vz).symm⟩
  obtain ⟨hcH,star⟩ := alternating_parity G hc r odd
  obtain ⟨T,sub,tr,nr,spoke,keep⟩ := fork_tree H hcH r m s t C L f dis free (star s rs) (star t rt) st arm
  have bound := marked_tree_budget G T hc hn r odd A ai (fun _ _ e => (sub e).1) tr nr (fun e => (sub e).2) bad
  have three (i j k l : V) (jk : j≠k) (jl : j≠l) (kl : k≠l) (ij : T.Adj i j) (ik : T.Adj i k) (il : T.Adj i l) : 3≤T.degree i := by
    have inc : ({j,k,l}:Finset V)⊆T.neighborFinset i := insert_subset ((T.mem_neighborFinset i j).mpr ij)
      (insert_subset ((T.mem_neighborFinset i k).mpr ik) (singleton_subset_iff.mpr ((T.mem_neighborFinset i l).mpr il)))
    have card := card_le_card inc
    rw [card_insert_of_not_mem (by simp [jk,jl]),card_pair kl,card_neighborFinset_eq_degree] at card
    exact card
  have ay : a≠y := by intro eq; rw [eq] at da; omega
  have bz : b≠z := by intro eq; rw [eq] at db; omega
  have du := three u m a y am.symm my ay (spoke u (by simp [C]) eu.symm)
    (fa ▸ (keep a (by simp [L])).symm) (fy ▸ (keep y (by simp [L])).symm)
  have dV := three v m b z bm.symm mz bz (spoke v (by simp [C]) ev.symm)
    (fb ▸ (keep b (by simp [L])).symm) (fz ▸ (keep z (by simp [L])).symm)
  have inc : ({u,v}:Finset V)⊆A∪P := insert_subset um (singleton_subset_iff.mpr vm)
  have both := sum_le_sum_of_subset_of_nonneg (f:=fun x => T.degree x-2) inc (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert (by simpa using uv),sum_singleton] at both
  change (T.degree u-2)+(T.degree v-2)≤∑ i∈A∪P,(T.degree i-2) at both
  change 1+(∑ i∈A∪P,(T.degree i-2))+bipartiteNum G<Fintype.card V at bound
  omega

#print axioms pred_vertical
#print axioms deep_fork_parents
end Minimal180.HigherRank
