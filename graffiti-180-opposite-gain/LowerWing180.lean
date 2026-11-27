import OppositeMasks180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If b is two layers beyond a, a connected active wing containing
one predecessor of b has only that one b-contact. No nonroot
independent mark is assumed to have degree two. -/
theorem lower_wing (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a b z : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (am : a∈A) (ap : a∈parity G r p) (bm : b∉A) (bp : b∈parity G r p)
    (na : ¬G.Adj a b) (sat : G.degree a=allowance G r p A+2) (db : G.dist b r=G.dist a r+2)
    (bz : G.Adj b z) (dz : G.dist b r=G.dist z r+1) (high : ∀ j∈A,j≠r → G.degree j≠2)
    (S : Finset V) (con : Con G S) (sr : S⊆univ\{a,b}) (zs : z∈S)
    (closed : ∀ i∈S,∀ j∈univ\({a,b}:Finset V),G.Adj i j → j∈S)
    (cap : (G.neighborFinset a∩S).card≤2) : (G.neighborFinset b∩S).card≤1 := by
  classical
  let R := univ\({a,b}:Finset V)
  have port {v : V} (av : G.Adj a v) : v∈R := mem_sdiff.mpr ⟨mem_univ _,fun e =>
    (mem_insert.mp e).elim (fun eq => av.ne eq.symm) (fun m => na ((mem_singleton.mp m) ▸ av))⟩
  have br : b≠r := fun e => by rw [e,dist_self] at db;omega
  have pred (j : V) (edge : G.Adj b j) (dj : G.dist b r=G.dist j r+1) : j∈A :=
    outside_predecessors_marked G gc hn r a ar p A ai am sat br na bp bm edge dj
  have za := pred _ bz dz
  have zp : z∉parity G r p := fun m => by have e := eq_dist G gc r b z p bz (iff_of_true bp m);omega
  have zr : z≠r := fun e => by rw [e,dist_self] at dz;omega
  have znext : G.dist z r=G.dist a r+1 := by omega
  have zh : 3≤G.degree z := by
    have up := forward_degree G gc r z b zr bz.symm (by omega)
    have notTwo := high z za zr;omega
  obtain ⟨w,u,aw,zw,wp,dw,au,wu,du⟩ := paired_ports G gc hn r a z ar zr p A ai am ap za zp sat zh znext
  have ws := closed _ zs _ (port aw) zw
  have us := closed _ ws _ (port au) wu
  have wuN : w≠u := fun e => by rw [e] at dw;omega
  have cover {t : V} (at' : G.Adj a t) (ts : t∈S) : t=w ∨ t=u := by
    have eq : ({w,u}:Finset V)=G.neighborFinset a∩S := eq_of_subset_of_card_le
      (insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr aw,ws⟩)
      (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr au,us⟩))) (by simpa only [card_pair wuN] using cap)
    have m : t∈({w,u}:Finset V) := eq ▸ mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr at',ts⟩
    exact (mem_insert.mp m).imp_right mem_singleton.mp
  have unique {j : V} (js : j∈S) (ja : j∈A) (dj : G.dist j r=G.dist a r+1) (jh : 2≤G.degree j) : j=z := by
    have jr : j≠r := fun e => by rw [e,dist_self] at dj;omega
    have jp : j∉parity G r p := fun m => by
      have f := (mem_parity ..).mp ap;have g := (mem_parity ..).mp m;omega
    obtain ⟨t,_,at',jt,_,dt,_,_,_⟩ := paired_ports G gc hn r a j ar jr p A ai am ap ja jp sat (by have := high _ ja jr;omega) dj
    have eq := (cover at' (closed _ js _ (port at') jt)).resolve_right (fun e => by rw [e] at dt;omega)
    subst t
    have small := horizontal_port G gc hn r a w ar p A ai am ap aw wp sat
    exact card_le_one.mp small j (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr jt.symm,jp,ai a am j ja (fun e => jp (e ▸ ap))⟩)
      z (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr zw.symm,zp,ai a am z za (fun e => zp (e ▸ ap))⟩)
  have thin (y : V) (ys : y∈S) (dy : G.dist y r=G.dist b r) : G.degree y≤1 := by
    by_contra! yl
    have yr : y≠r := fun e => by rw [e,dist_self] at dy;omega
    have ay : a≠y := fun e => by rw [←e] at dy;omega
    have yp : y∈parity G r p := (mem_parity ..).mpr (dy ▸ (mem_parity ..).mp bp)
    by_cases ya : y∈A
    · obtain ⟨t,at',yt⟩ := common_port G gc hn r a y ar yr ay p A ai am ya sat (by have := high _ ya yr;omega)
      have d1 := gc.dist_triangle (u:=t) (v:=a) (w:=r)
      have d2 := gc.dist_triangle (u:=y) (v:=t) (w:=r)
      rw [dist_eq_one_iff_adj.mpr at'.symm] at d1
      rw [dist_eq_one_iff_adj.mpr yt] at d2
      rcases cover at' (closed _ ys _ (port at') yt) with e|e <;> subst t <;> omega
    · have no : ¬G.Adj a y := fun e => by have ds := eq_dist G gc r a y p e (iff_of_true ap yp);omega
      obtain ⟨j,yj,step⟩ := Graffiti169.exists_predecessor G gc r y yr
      have ja := outside_predecessors_marked G gc hn r a ar p A ai am sat yr no yp ya yj step
      have dj : G.dist j r=G.dist a r+1 := by omega
      have jm : j∈R := mem_sdiff.mpr ⟨mem_univ _,fun m => by
        rcases mem_insert.mp m with e|e
        · rw [e] at dj;omega
        · rw [mem_singleton.mp e] at dj;omega⟩
      have jr : j≠r := fun e => by rw [e,dist_self] at dj;omega
      have eq := unique (closed _ ys _ jm yj) ja dj (forward_degree G gc r j y jr yj.symm (by omega))
      subst j
      have byeq := unique_successor G gc hn r a z b y ar zr (fun e => zp (e ▸ ap)) p A ai am za sat bm ya na no bz yj dz step
      exact (mem_sdiff.mp (sr ys)).2 (byeq ▸ mem_insert_of_mem (mem_singleton_self _))
  have below := lower_contact G gc r b z S con zs (by omega) thin
  have incl : G.neighborFinset b∩S⊆{z} := by
    intro i im
    obtain ⟨nb,is⟩ := mem_inter.mp im
    have ei := (G.mem_neighborFinset ..).mp nb
    have di := gc.dist_triangle (u:=b) (v:=i) (w:=r)
    rw [dist_eq_one_iff_adj.mpr ei] at di
    have low := below i is ei
    have step : G.dist b r=G.dist i r+1 := by omega
    have ir : i≠r := fun e => by rw [e,dist_self] at step;omega
    exact mem_singleton.mpr (unique is (pred i ei step) (by omega) (forward_degree G gc r i b ir ei.symm low.le))
  simpa only [card_singleton] using card_le_card incl

#print axioms lower_wing
end Minimal180.OppositeGain
