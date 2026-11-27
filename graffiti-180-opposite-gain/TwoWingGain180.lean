import LeafLayer180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The second tip is absent from the marked paths in layers d(a)+1 and d(a)+2. -/
def TipAvoids (G : SimpleGraph V) (r a b : V) (p : Bool) (A : Finset V) : Prop :=
  b∉A∪parity G r p ∨ (G.dist b r≠G.dist a r+1 ∧ G.dist b r≠G.dist a r+2)

/-- In two mixed separated regions, if no nonroot independent mark
has degree two and b cannot lie on the two marked layers, the
protected repair exists. The number of distance layers is unrestricted. -/
theorem two_no_degree_two_repair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a b : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A)
    (ab : a≠b) (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (c : V→Bool) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (high : ∀ z∈A,z≠r → G.degree z≠2) (avoid : TipAvoids G r a b p A) : Protected G r p A := by
  classical
  by_contra bad
  obtain ⟨deg,two,_⟩ := solo_rigidity G gc hn r p A ai bad a b ab bi ak bk
  have sat : G.degree a=allowance G r p A+2 := by omega
  have na := (pair_obstruction G gc hn r p A ai bad a b ab bi).1
  have am := (mem_inter.mp ak).1
  have ap := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  let R := univ\({a,b}:Finset V)
  have inR {v : V} (va : v≠a) (vb : v≠b) : v∈R := mem_sdiff.mpr
    ⟨mem_univ _,fun m => (mem_insert.mp m).elim va (fun q => vb (mem_singleton.mp q))⟩
  have port {v : V} (av : G.Adj a v) : v∈R := inR av.ne.symm (fun eq => na (eq ▸ av))
  have deep {v : V} (vm : v∈A∪parity G r p)
      (dv : G.dist v r=G.dist a r+1 ∨ G.dist v r=G.dist a r+2) : v∈R := by
    apply inR
    · intro eq;subst v;omega
    · intro eq;subst v
      rcases avoid with outside|⟨n1,n2⟩
      · exact outside vm
      · exact dv.elim n1 n2
  obtain ⟨s,mono,cap⟩ := two_port_regions G a b deg C D O h c lc rc
  obtain ⟨x,y,z,ed,xp,yp,xa,ax,ay,dxy,_,zr,za,zp,xz,dxz,_,alt⟩ :=
    remote_obstruction G gc hn r a b ar p A ai ab bi ak bk bad
  have zh : 3≤G.degree z := by
    have up := forward_degree G gc r z x zr xz.symm (by omega)
    have notTwo := high z za zr;omega
  have far := (alt.resolve_left (by omega)).1
  have dy : G.dist y r=G.dist a r+2 := dxy ▸ far
  have dz : G.dist z r=G.dist a r+1 := by omega
  have xr := deep (mem_union_right A xp) (Or.inr far)
  have yr := deep (mem_union_right A yp) (Or.inr dy)
  have zz := deep (mem_union_left _ za) (Or.inl dz)
  obtain ⟨w,u,aw,zw,wp,dw,au,wu,du⟩ := paired_ports G gc hn r a z ar zr p A ai am ap za zp sat zh dz
  have uw : u≠w := fun eq => by rw [eq] at du;omega
  have chain : s w=s y := (mono w (port aw) z zz zw.symm).trans
    ((mono z zz x xr xz.symm).trans (mono x xr y yr ed))
  have su : s u=s w := mono u (port au) w (port aw) wu.symm
  by_cases ya : y∈A
  · have yr0 : y≠r := fun eq => by rw [eq,dist_self] at dy;omega
    have ay0 : a≠y := fun eq => by rw [←eq] at dy;omega
    have yh : 3≤G.degree y := by
      have up := forward_degree G gc r y x yr0 ed.symm dxy.ge
      have notTwo := high y ya yr0;omega
    obtain ⟨t,at',yt⟩ := common_port G gc hn r a y ar yr0 ay0 p A ai am ya sat yh
    have av' := gc.dist_triangle (u:=t) (v:=a) (w:=r)
    have yt' := gc.dist_triangle (u:=y) (v:=t) (w:=r)
    rw [dist_eq_one_iff_adj.mpr at'.symm] at av'
    rw [dist_eq_one_iff_adj.mpr yt] at yt'
    have dt : G.dist t r=G.dist a r+1 := by omega
    exact no_three_ports G a s cap u w t au aw at' uw (fun eq => by rw [eq] at du;omega)
      (fun eq => by rw [eq] at dw;omega) su (chain.trans (mono y yr t (port at') yt))
  · obtain ⟨j,jr,ja,jp,yj,dj,_⟩ := missed_edge_parent G gc hn r a ar p A ai am ap sat yp xp ed.symm ya ay
    have dj' : G.dist j r=G.dist a r+1 := by omega
    have jh : 3≤G.degree j := by
      have up := forward_degree G gc r j y jr yj.symm (by omega)
      have notTwo := high j ja jr;omega
    obtain ⟨t,_,at',jt,_,dt,_,_,_⟩ := paired_ports G gc hn r a j ar jr p A ai am ap ja jp sat jh dj'
    have tz : w≠t := by
      intro eq;subst t
      have small := horizontal_port G gc hn r a w ar p A ai am ap aw wp sat
      have nz := ai a am z za (fun eq => zp (eq ▸ ap))
      have nj := ai a am j ja (fun eq => jp (eq ▸ ap))
      have same := card_le_one.mp small z (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr zw.symm,zp,nz⟩)
        j (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr jt.symm,jp,nj⟩)
      subst j
      exact ed.ne (unique_successor G gc hn r a z x y ar zr (fun e => zp (e ▸ ap)) p A ai am za sat xa ya ax ay xz yj dxz dj)
    have jj := deep (mem_union_left _ ja) (Or.inl dj')
    exact no_three_ports G a s cap u w t au aw at' uw (fun eq => by rw [eq] at du;omega) tz su
      (chain.trans ((mono y yr j jj yj).trans (mono j jj t (port at') jt)))

/-- In each stated case, incompatible deletion signs in two active
regions force at least three units of the exact eligible-leaf allowance. -/
theorem masks_force_three (G : SimpleGraph V) (gc : G.Connected) (r a b : V) (ar : a≠r)
    (p : Bool) (A : Finset V) (ai : Indep G A) (ab : a≠b) (na : ¬G.Adj a b)
    (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p))
    (deg : G.degree a=4) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (scope : RepairScope G r a p A ∨ ((∀ z∈A,z≠r → G.degree z≠2) ∧ TipAvoids G r a b p A))
    (absent : ¬∃ t : Bool,DropCheck G a b (A∩insert r (parity G r p)) C c t ∧
       DropCheck G a b (A∩insert r (parity G r p)) D c t) : 3≤allowance G r p A := by
  have high : 2<Fintype.card V := by have := G.degree_lt_card_verts a;omega
  have paid := protected_degree G gc high r a p A ai ak
  have pm := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  by_contra! small
  have two : allowance G r p A=2 := by omega
  apply absent
  apply (active_contacts_iff G gc (by omega) r p A ai a b ab na bi (mem_inter.mp ak).1 pm deg two C D O h c cp lc rc).mp
  rcases scope with sc | ⟨hs,tip⟩
  · exact solo_scope G gc (by omega) r a b ar p A ai ab bi ak bk sc
  · exact two_no_degree_two_repair G gc (by omega) r a b ar p A ai ab bi ak bk C D O h c lc rc hs tip

#print axioms two_no_degree_two_repair
#print axioms masks_force_three
end Minimal180.OppositeGain
