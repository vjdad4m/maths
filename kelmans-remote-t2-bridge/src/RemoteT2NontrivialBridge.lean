import RemoteT2PairCounts
import RemoteT2Scope
import RemoteT2PairStructure

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2NontrivialBridge
open RemoteT2PairCounts (innerCut row OutsideTwo outside_cut_balance)
open SquareCap (boundary SmallTrivial)
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
private def changeColor (c d : V→Bool) (w : V) : Bool := Bool.xor (c w) (d w)

omit [Fintype V] [DecidableEq V] in
private theorem differ_at (c d : V→Bool) (w : V) :
    changeColor c d w = true ↔ c w ≠ d w := by
  cases h : c w <;> cases k : d w <;> simp [changeColor,h,k]

omit [Fintype V] [DecidableEq V] in
private def reorient (c : V→Bool) (e : V×V) : V×V := if c e.1 then e else e.swap

omit [DecidableRel G.Adj] in
private theorem inner_mem (c : V→Bool) (x y p q : V) :
    (p,q)∈innerCut G c x y ↔
      (c p=true ∧ c q=false ∧ G.Adj p q) ∧ (p≠x ∧ p≠y ∧ q≠x ∧ q≠y) := by
  classical
  simp [innerCut,boundary]

omit [DecidableRel G.Adj] in
private theorem reorient_mem (c : V→Bool) (x y : V) (p q : V) (pq : G.Adj p q)
    (px : p≠x) (py : p≠y) (qx : q≠x) (qy : q≠y) (diff : c p≠c q) :
    reorient c (p,q) ∈ innerCut G c x y := by
  cases h : c p <;> cases k : c q <;> simp [h,k] at diff
  · simpa [reorient,h] using (inner_mem G c x y q p).mpr ⟨⟨k,h,pq.symm⟩,qx,qy,px,py⟩
  · simpa [reorient,h] using (inner_mem G c x y p q).mpr ⟨⟨h,k,pq⟩,px,py,qx,qy⟩

omit [Fintype V] [DecidableEq V] in
private theorem reorient_twice (c h : V→Bool) (p q : V) (pt : h p=true) (qf : h q=false) :
    reorient h (reorient c (p,q)) = (p,q) := by
  cases cp : c p <;> simp [reorient,cp,pt,qf,Prod.swap]

omit [Fintype V] [DecidableEq V] in
private theorem color_change_crosses (c d : V→Bool) (p q : V)
    (h : changeColor c d p = true) (k : changeColor c d q = false) :
    c p≠c q ∨ d p≠d q := by
  by_contra! e
  unfold changeColor at h k
  rw [e.1,e.2,k] at h
  contradiction

omit [DecidableRel G.Adj] in
/-- If two surviving cuts of width two share a marked edge, orienting it the
same way makes the XOR of their vertex-colorings have width at most two:
the common edge cancels and each original cut contributes at most one. -/
theorem xor_width_at_most_two {c d : V→Bool} {x y u v : V}
    (huv : G.Adj u v) (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (cu : c u=true) (cv : c v=false) (du : d u=true) (dv : d v=false)
    (C : (innerCut G c x y).card=2) (D : (innerCut G d x y).card=2) :
    (innerCut G (changeColor c d) x y).card≤2 := by
  classical
  let h := changeColor c d
  have hu : h u=false := by simp [h,changeColor,cu,du]
  have hv : h v=false := by simp [h,changeColor,cv,dv]
  have pick (k : V→Bool) (kt : k u=true) (kf : k v=false)
      (W : (innerCut G k x y).card=2) :
      ∃ a : V×V, (innerCut G k x y).erase (u,v) = {a} := by
    apply card_eq_one.mp
    rw [card_erase_of_mem ((inner_mem G k x y u v).mpr ⟨⟨kt,kf,huv⟩,ux,uy,vx,vy⟩),W]
  obtain ⟨a,ha⟩ := pick c cu cv C
  obtain ⟨b,hb⟩ := pick d du dv D
  have support (k : V→Bool) (z : V×V) (hz : (innerCut G k x y).erase (u,v)={z})
      (p q : V) (pt : h p=true) (qf : h q=false) (pq : G.Adj p q)
      (px : p≠x) (py : p≠y) (qx : q≠x) (qy : q≠y) (diff : k p≠k q) :
      (p,q)=reorient h z := by
    have kMem := reorient_mem G k x y p q pq px py qx qy diff
    have kNe : reorient k (p,q) ≠ (u,v) := by
      intro eq
      have e := congrArg (reorient h) eq
      rw [reorient_twice k h p q pt qf] at e
      have pEq : p = v := by simpa [reorient,hu,Prod.swap] using congrArg Prod.fst e
      rw [pEq,hv] at pt
      contradiction
    have em : reorient k (p,q) ∈ ({z} : Finset (V×V)) := by
      rw [←hz]
      exact mem_erase.mpr ⟨kNe,kMem⟩
    rw [←mem_singleton.mp em,reorient_twice k h p q pt qf]
  have sub : innerCut G h x y ⊆ {reorient h a,reorient h b} := by
    intro e he
    obtain ⟨p,q⟩ := e
    obtain ⟨⟨pt,qf,pq⟩,px,py,qx,qy⟩ := (inner_mem G h x y p q).mp he
    rcases color_change_crosses c d p q pt qf with diff|diff
    · exact mem_insert.mpr (Or.inl (support c a ha p q pt qf pq px py qx qy diff))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (support d b hb p q pt qf pq px py qx qy diff)))
  exact (card_le_card sub).trans card_le_two

private theorem pair_opp_of_rows (c : V→Bool) {x y a b : V}
    (X : (G.neighborFinset x).erase y={a,b})
    (f : (row G c x y false).card=1) (t : (row G c x y true).card=1) :
    c a≠c b := by
  intro eq
  unfold row at f t
  rw [X] at f t
  have zero : ({a,b}:Finset V).filter (fun w=>c w≠c a)=∅ := by
    ext w
    simp only [mem_filter,mem_insert,mem_singleton,not_mem_empty,iff_false]
    rintro ⟨rfl|rfl,h⟩
    · exact h rfl
    · exact h eq.symm
  cases ea : c a <;> rw [ea] at zero
  · rw [zero] at f
    simp at f
  · rw [zero] at t
    simp at t

omit [Fintype V] [DecidableEq V] in
private theorem pair_change_same (c d : V→Bool) (a b : V)
    (hc : c a≠c b) (hd : d a≠d b) :
    changeColor c d a=changeColor c d b := by
  cases ca : c a <;> cases cb : c b <;> cases da : d a <;> cases db : d b <;>
    simp_all [changeColor]

/-- There is at most one nontrivial bridge cut after an adjacent vertex
pair and an additional surviving edge are removed from a cyclic-four cubic
graph. Here the bridge cuts are expressed in the unpurged graph as width
two cuts crossing that additional edge; both surviving shores have two or
more vertices. -/
theorem unique_balanced_cut (small : SmallTrivial G) (cub : ∀ w : V, G.degree w=3)
    {x y u v : V} (xy : G.Adj x y) (uv : G.Adj u v)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y) {c d : V→Bool}
    (cu : c u=true) (cv : c v=false) (du : d u=true) (dv : d v=false)
    (cp : OutsideTwo c x y true) (cn : OutsideTwo c x y false)
    (dp : OutsideTwo d x y true) (dn : OutsideTwo d x y false)
    (C : (innerCut G c x y).card=2) (D : (innerCut G d x y).card=2) :
    ∀ w : V, w≠x → w≠y → c w=d w := by
  classical
  have mkPair {a b : V} (e : G.Adj a b) :
      ∃ p q : V,p≠q ∧ (G.neighborFinset a).erase b={p,q} := by
    apply card_eq_two.mp
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr e),card_neighborFinset_eq_degree,cub]
  obtain ⟨a,b,ab,X⟩ := mkPair xy
  obtain ⟨s,t,st,Y⟩ := mkPair xy.symm
  obtain ⟨cff,ctt,cyf,cyt⟩ := (outside_cut_balance G small c xy (cub x) (cub y) cp cn).2 C
  obtain ⟨dff,dtt,dyf,dyt⟩ := (outside_cut_balance G small d xy (cub x) (cub y) dp dn).2 D
  let h := changeColor c d
  have hab : h a=h b := pair_change_same c d a b
    (pair_opp_of_rows G c X cff ctt) (pair_opp_of_rows G d X dff dtt)
  have hst : h s=h t := pair_change_same c d s t
    (pair_opp_of_rows G c Y cyf cyt) (pair_opp_of_rows G d Y dyf dyt)
  have hu : h u=false := by simp [h,changeColor,cu,du]
  have hv : h v=false := by simp [h,changeColor,cv,dv]
  have upper : (innerCut G h x y).card≤2 := xor_width_at_most_two G uv ux uy vx vy cu cv du dv C D
  have noPair : ¬ OutsideTwo h x y true := by
    intro p
    have n : OutsideTwo h x y false := ⟨u,v,ux,uy,vx,vy,uv.ne,hu,hv⟩
    have g := outside_cut_balance G small h xy (cub x) (cub y) p n
    have eq : (innerCut G h x y).card=2 := by omega
    obtain ⟨hf,ht,_,_⟩ := g.2 eq
    exact pair_opp_of_rows G h X hf ht hab
  intro w wx wy
  by_contra ne
  have wt : h w=true := (differ_at c d w).mpr ne
  have unique (z : V) (zx : z≠x) (zy : z≠y) (zt : h z=true) : z=w := by
    by_contra n
    exact noPair ⟨z,w,zx,zy,wx,wy,n,zt,wt⟩
  have portApart {j k p q : V} (jk : G.Adj j k)
      (ex : x=j∧y=k ∨ x=k∧y=j)
      (P : (G.neighborFinset j).erase k={p,q}) (pq : p≠q) (hf : h p=h q) :
      ¬ G.Adj w j := by
    intro wj
    have outside (z : V) (hz : z∈({p,q}:Finset V)) : z≠x ∧ z≠y := by
      rw [←P] at hz
      obtain ⟨n,e⟩ := mem_erase.mp hz
      have m := ((mem_neighborFinset _ _ _).mp e).ne.symm
      rcases ex with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨m,n⟩
      · exact ⟨n,m⟩
    have wk : w≠k := by rcases ex with ⟨_,rfl⟩|⟨rfl,_⟩ <;> assumption
    have wm : w∈({p,q}:Finset V) := by
      rw [←P]
      exact mem_erase.mpr ⟨wk,(mem_neighborFinset _ _ _).mpr wj.symm⟩
    have pp := outside p (by simp)
    have qq := outside q (by simp)
    have pt : h p=true := by
      rcases mem_insert.mp wm with rfl|qw
      · exact wt
      · rw [hf,←mem_singleton.mp qw]
        exact wt
    have qt : h q=true := hf.symm.trans pt
    exact pq ((unique p pp.1 pp.2 pt).trans (unique q qq.1 qq.2 qt).symm)
  have noX := portApart xy (Or.inl ⟨rfl,rfl⟩) X ab hab
  have noY := portApart xy.symm (Or.inr ⟨rfl,rfl⟩) Y st hst
  have sub : (G.neighborFinset w).image (fun z=>(w,z)) ⊆ innerCut G h x y := by
    intro e he
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    have wz := (mem_neighborFinset _ _ _).mp hz
    have zx : z≠x := fun p=>noX (p ▸ wz)
    have zy : z≠y := fun p=>noY (p ▸ wz)
    have zf : h z=false := by
      cases k : h z
      · rfl
      · exact False.elim (wz.ne.symm (unique z zx zy k))
    exact (inner_mem G h x y w z).mpr ⟨⟨wt,zf,wz⟩,wx,wy,zx,zy⟩
  have lb := card_le_card sub
  rw [card_image_of_injective _ (fun _ _ eq=>congrArg Prod.snd eq),card_neighborFinset_eq_degree,cub] at lb
  omega


/-- Coexistence of a leaf bridge at a surviving endpoint of the omitted edge
and a nontrivial bridge forces the leaf-side shore of the latter to have
exactly two vertices. This conclusion applies to any cubic cyclic-four graph. -/
theorem leaf_and_balanced_cut_small_shore (small : SmallTrivial G)
    (big : 5≤Fintype.card V) (cub : ∀ w : V, G.degree w=3)
    {x y u v : V} (xy : G.Adj x y) (uv : G.Adj u v)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (uyEdge : G.Adj u y) {c : V→Bool} (cu : c u=true) (cv : c v=false)
    (cp : OutsideTwo c x y true) (cn : OutsideTwo c x y false)
    (C : (innerCut G c x y).card=2)
    (leafWidth : (innerCut G (fun z=>decide (z=u)) x y).card=2) :
    ∃ w : V,w≠x ∧ w≠y ∧ w≠u ∧ G.Adj x w ∧ G.Adj u w ∧
      ∀ z : V,z≠x → z≠y → (c z=true ↔ z=u ∨ z=w) := by
  classical
  let d : V→Bool := fun z=>decide (z=u)
  let h := changeColor c d
  have du : d u=true := by simp [d]
  have dv : d v=false := by simp [d,uv.ne.symm]
  have hc : ∀ z : V,z≠u → h z=c z := by
    intro z n
    simp [h,changeColor,d,n]
  have hu : h u=false := by simp [h,changeColor,cu,du]
  have hv : h v=false := by rw [hc v uv.ne.symm,cv]
  have upper : (innerCut G h x y).card≤2 :=
    xor_width_at_most_two G uv ux uy vx vy cu cv du dv C leafWidth
  obtain ⟨xf,xt,yf,yt⟩ := (outside_cut_balance G small c xy (cub x) (cub y) cp cn).2 C
  have mkPair {a b : V} (e : G.Adj a b) :
      ∃ p q : V,p≠q ∧ (G.neighborFinset a).erase b={p,q} := by
    apply card_eq_two.mp
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr e),card_neighborFinset_eq_degree,cub]
  obtain ⟨a,b,ab,Y⟩ := mkPair xy.symm
  have ua : u=a ∨ u=b := by
    have t : u∈(G.neighborFinset y).erase x :=
      mem_erase.mpr ⟨ux,(mem_neighborFinset _ _ _).mpr uyEdge.symm⟩
    simpa [Y] using t
  have same : h a=h b := by
    have cb := pair_opp_of_rows G c Y yf yt
    rcases ua with rfl|rfl
    · rw [hu,hc _ ab.symm]
      cases e : c b <;> simp_all
    · rw [hu,hc _ ab]
      cases e : c a <;> simp_all
  have ntwo : ¬ OutsideTwo h x y true := by
    intro tp
    have tn : OutsideTwo h x y false := ⟨u,v,ux,uy,vx,vy,uv.ne,hu,hv⟩
    have k := outside_cut_balance G small h xy (cub x) (cub y) tp tn
    have eq : (innerCut G h x y).card=2 := by omega
    obtain ⟨_,_,hf,ht⟩ := k.2 eq
    exact pair_opp_of_rows G h Y hf ht same
  have existsW : (row G c x y false).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w,hw⟩ := existsW
  obtain ⟨wMem,wColor⟩ := mem_filter.mp hw
  have xw := (mem_neighborFinset _ _ _).mp (mem_erase.mp wMem).2
  have wy : w≠y := (mem_erase.mp wMem).1
  have wx : w≠x := xw.ne.symm
  have wo : w≠u := by
    intro e
    subst w
    have both : G.Adj x u ∧ G.Adj y u := ⟨xw,uyEdge.symm⟩
    exact RemoteT2Scope.cyclic_four_pair_no_common small big cub xy u both
  have wc : c w=true := Bool.eq_true_of_not_eq_false wColor
  have precise (z : V) (zx : z≠x) (zy : z≠y) : c z=true ↔ z=u ∨ z=w := by
    constructor
    · intro zc
      by_cases zu : z=u
      · exact Or.inl zu
      · apply Or.inr
        by_contra zw
        exact ntwo ⟨z,w,zx,zy,wx,wy,zw,(hc z zu).trans zc,(hc w wo).trans wc⟩
    · rintro (rfl|rfl) <;> assumption
  have uw : G.Adj u w := by
    by_contra n
    have noCommon : ¬(G.Adj w x ∧ G.Adj w y) := by
      rintro ⟨l,r⟩
      exact RemoteT2Scope.cyclic_four_pair_no_common small big cub xy w ⟨l.symm,r.symm⟩
    have deg := RemoteT2PairStructure.surviving_card_lb G (cub w) noCommon
    have e : (u,v)∈innerCut G c x y :=
      (inner_mem G c x y u v).mpr ⟨⟨cu,cv,uv⟩,ux,uy,vx,vy⟩
    have bnd : ((innerCut G c x y).erase (u,v)).card=1 := by
      rw [card_erase_of_mem e,C]
    have sub : (RemoteT2PairStructure.surviving G x y w).image (fun z=>(w,z)) ⊆
        (innerCut G c x y).erase (u,v) := by
      intro e' he
      obtain ⟨z,hz,rfl⟩ := mem_image.mp he
      obtain ⟨zy,zN⟩ := mem_erase.mp hz
      obtain ⟨zx,mem⟩ := mem_erase.mp zN
      have wz := (mem_neighborFinset _ _ _).mp mem
      have cz : c z=false := by
        cases color : c z
        · rfl
        · rcases (precise z zx zy).mp color with rfl|rfl
          · exact False.elim (n wz.symm)
          · exact False.elim (wz.ne rfl)
      exact mem_erase.mpr ⟨fun eq=>wo (congrArg Prod.fst eq),
        (inner_mem G c x y w z).mpr ⟨⟨wc,cz,wz⟩,wx,wy,zx,zy⟩⟩
    have le := card_le_card sub
    rw [card_image_of_injective _ (fun _ _ eq=>congrArg Prod.snd eq),bnd] at le
    omega
  exact ⟨w,wx,wy,wo,xw,uw,precise⟩

#print axioms leaf_and_balanced_cut_small_shore

#print axioms xor_width_at_most_two
#print axioms unique_balanced_cut
end
end KelmansCactus.AtomicBridge.RemoteT2NontrivialBridge
