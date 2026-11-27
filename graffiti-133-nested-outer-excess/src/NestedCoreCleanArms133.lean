import NestedCoreThreeGate133
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133NestedFour
open SimpleGraph Finset Graffiti133
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
variable {V : Type*} {G : SimpleGraph V}

def Arm (W : Set V) (g : V) : Prop :=
  ∃ p : Fin 4→V, InducedPath G p ∧ (∀ i,p i∈W) ∧ (∀ i,G.Adj g (p i) ↔ i=0)

private theorem path4_tuple {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : ¬G.Adj a c) (ad : ¬G.Adj a d) (bd : ¬G.Adj b d)
    (nac : a≠c) (nad : a≠d) (nbd : b≠d) :
    InducedPath G (![a,b,c,d] : Fin 4→V) := by
  have nab := ab.ne
  have nbc := bc.ne
  have ncd := cd.ne
  constructor
  · intro i j e
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j ij
    fin_cases i <;> fin_cases j <;> norm_num at ij ⊢ <;> simp_all

private theorem arm_of_four_colors {W : Set V} {g a b c d : V} {tag : V→V}
    (hit : ∀ x∈W,G.Adj g x ↔ tag x=g)
    (aw : a∈W) (bw : b∈W) (cw : c∈W) (dw : d∈W)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : ¬G.Adj a c) (ad : ¬G.Adj a d) (bd : ¬G.Adj b d)
    (nac : a≠c) (nad : a≠d) (nbd : b≠d)
    (ta : tag a=g) (tb : tag b≠g) (tc : tag c≠g) (td : tag d≠g) :
    Arm (G:=G) W g := by
  refine ⟨![a,b,c,d],path4_tuple ab bc cd ac ad bd nac nad nbd,?_,?_⟩
  · intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i
    · simpa [ta] using hit a aw
    · simpa [tb] using hit b bw
    · simpa [tc] using hit c cw
    · simpa [td] using hit d dw

theorem arm_from_branch_neighbor {W : Set V} (h4 : FourCycleFree G) (tag : V→V)
    (tri : ∀ a∈W,∀ b∈W,∀ c∈W,G.Adj a b→G.Adj b c→¬G.Adj a c)
    (proper : ∀ a∈W,∀ b∈W,G.Adj a b→tag a≠tag b)
    (sq : ∀ a∈W,∀ b∈W,∀ c∈W,a≠c→G.Adj b a→G.Adj b c→tag a≠tag c)
    {v x y w z : V} (vv : v∈W) (xv : x∈W) (yv : y∈W) (wv : w∈W) (zv : z∈W)
    (vx : G.Adj v x) (vy : G.Adj v y) (vw : G.Adj v w)
    (yz : G.Adj y z) (zvne : z≠v)
    (xyne : x≠y) (xwne : x≠w) (ywne : y≠w)
    (hit : ∀ a∈W,G.Adj (tag x) a ↔ tag a=tag x) :
    Arm (G:=G) W (tag x) := by
  have tvx := proper v vv x xv vx
  have txy := sq x xv v vv y yv xyne vx vy
  have txw := sq x xv v vv w wv xwne vx vw
  have twy := sq w wv v vv y yv ywne.symm vw vy
  by_cases zx : tag z=tag x
  · have zw : z≠w := fun eq=>txw (zx.symm.trans (congrArg tag eq))
    have nZV := tri z zv y yv v vv yz.symm vy.symm
    have nYW := tri y yv v vv w wv vy.symm vw
    have nZW : ¬G.Adj z w := by
      intro yes
      have ne : y≠w := ywne
      exact zvne (h4 y w z v ne yz yes.symm vy.symm vw.symm)
    exact arm_of_four_colors hit zv yv vv wv yz.symm vy.symm vw nZV nZW nYW
      zvne zw ywne zx txy.symm tvx txw.symm
  · have xz : x≠z := fun eq=>zx (congrArg tag eq).symm
    have nXY := tri x xv v vv y yv vx.symm vy
    have nVZ := tri v vv y yv z zv vy yz
    have nXZ : ¬G.Adj x z := by
      intro yes
      exact zvne (h4 x y z v xyne yes yz vx.symm vy.symm)
    exact arm_of_four_colors hit xv vv yv zv vx.symm vy yz nXY nXZ nVZ
      xyne xz zvne.symm rfl tvx txy.symm zx

private theorem arm_adj {p : Fin 4→V} (h : InducedPath G p) (i j : Fin 4) :
    G.Adj (p i) (p j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  rcases lt_trichotomy i j with lt|eq|gt
  · rw [h.2 i j lt]
    have l : (i.val < j.val) := lt
    have no : j.val+1≠i.val := by omega
    simp [no]
  · subst j
    simp
  · rw [SimpleGraph.adj_comm,h.2 j i gt]
    have l : (j.val < i.val) := gt
    have no : i.val+1≠j.val := by omega
    simp [no]

theorem two_clean_arms_induced_P9 {X Y : Set V} {g : V}
    (gx : g∉X) (gy : g∉Y) (dis : Disjoint X Y)
    (anti : ∀ x∈X,∀ y∈Y,¬G.Adj x y)
    (ap : Arm (G:=G) X g) (aq : Arm (G:=G) Y g) :
    ∃ f : Fin 9→V,InducedPath G f := by
  obtain ⟨p,hp,wp,ap⟩ := ap
  obtain ⟨q,hq,wq,aq⟩ := aq
  have ep (i j : Fin 4) : p i=p j ↔ i=j := hp.1.eq_iff
  have eq (i j : Fin 4) : q i=q j ↔ i=j := hq.1.eq_iff
  have pq (i j : Fin 4) : p i≠q j := fun e=>Set.disjoint_left.mp dis (wp i) (e.symm ▸ wq j)
  have qp (i j : Fin 4) : q i≠p j := (pq j i).symm
  have gp (i : Fin 4) : g≠p i := fun e=>gx (e.symm ▸ wp i)
  have gq (i : Fin 4) : g≠q i := fun e=>gy (e.symm ▸ wq i)
  have pg (i : Fin 4) : p i≠g := (gp i).symm
  have qg (i : Fin 4) : q i≠g := (gq i).symm
  have no (i j : Fin 4) : ¬G.Adj (p i) (q j) := anti _ (wp i) _ (wq j)
  have no' (i j : Fin 4) : ¬G.Adj (q i) (p j) := fun h=>no j i h.symm
  have pa (i : Fin 4) : G.Adj (p i) g ↔ i=0 := ⟨fun h=>(ap i).mp h.symm,fun h=>((ap i).mpr h).symm⟩
  have qa (i : Fin 4) : G.Adj (q i) g ↔ i=0 := ⟨fun h=>(aq i).mp h.symm,fun h=>((aq i).mpr h).symm⟩
  let f : Fin 9→V := ![p 3,p 2,p 1,p 0,g,q 0,q 1,q 2,q 3]
  refine ⟨f,?_,?_⟩
  · intro i j e
    fin_cases i <;> fin_cases j <;>
      simp [f,ep,eq,pq,qp,gp,gq,pg,qg] at e ⊢
  · intro i j ij
    fin_cases i <;> fin_cases j <;>
      norm_num at ij <;>
      norm_num [f,arm_adj hp,arm_adj hq,ap,aq,pa,qa,no,no'] <;> decide

structure Branch (G : SimpleGraph V) (W : Set V) where
  v : V
  x : V
  y : V
  z : V
  vW : v∈W
  xW : x∈W
  yW : y∈W
  zW : z∈W
  vx : G.Adj v x
  vy : G.Adj v y
  vz : G.Adj v z
  xy : x≠y
  xz : x≠z
  yz : y≠z
  hasNext : ∀ w, (w=x ∨ w=y ∨ w=z) → ∃ u∈W,u≠v ∧ G.Adj w u

theorem three_arm_colors_of_branch {W : Set V} (A : Finset V) (h4 : FourCycleFree G)
    (tag : V→V) (r : ∀ x∈W,tag x∈A) (off : ∀ x∈W,x∉A)
    (tri : ∀ a∈W,∀ b∈W,∀ c∈W,G.Adj a b→G.Adj b c→¬G.Adj a c)
    (proper : ∀ a∈W,∀ b∈W,G.Adj a b→tag a≠tag b)
    (gate : ∀ x∈W,∀ a∈A,G.Adj a x↔tag x=a)
    (B : Branch G W) :
    ∃ S : Finset V,S⊆A ∧ S.card=3 ∧ ∀ a∈S,Arm (G:=G) W a := by
  classical
  have sq (a : V) (aw : a∈W) (b : V) (bw : b∈W) (c : V) (cw : c∈W)
      (ac : a≠c) (ba : G.Adj b a) (bc : G.Adj b c) : tag a≠tag c := by
    intro eq
    have t : tag a∈A := r a aw
    have aedge := (gate a aw (tag a) t).mpr rfl
    have cedge := (gate c cw (tag a) t).mpr eq.symm
    exact ac (h4 b (tag a) a c (fun e=>off b bw (e ▸ t)) ba aedge bc cedge)
  have txy := sq B.x B.xW B.v B.vW B.y B.yW B.xy B.vx B.vy
  have txz := sq B.x B.xW B.v B.vW B.z B.zW B.xz B.vx B.vz
  have tyz := sq B.y B.yW B.v B.vW B.z B.zW B.yz B.vy B.vz
  have exX := B.hasNext B.x (Or.inl rfl)
  have exY := B.hasNext B.y (Or.inr (Or.inl rfl))
  obtain ⟨a,aw,an,xa⟩ := exX
  obtain ⟨b,bw,bn,yb⟩ := exY
  have ax : Arm (G:=G) W (tag B.x) :=
    arm_from_branch_neighbor h4 tag tri proper sq B.vW B.xW B.yW B.zW bw B.vx B.vy B.vz
      yb bn B.xy B.xz B.yz (fun w ww=>gate w ww _ (r _ B.xW))
  have ay : Arm (G:=G) W (tag B.y) :=
    arm_from_branch_neighbor h4 tag tri proper sq B.vW B.yW B.xW B.zW aw B.vy B.vx B.vz
      xa an B.xy.symm B.yz B.xz (fun w ww=>gate w ww _ (r _ B.yW))
  have az : Arm (G:=G) W (tag B.z) :=
    arm_from_branch_neighbor h4 tag tri proper sq B.vW B.zW B.xW B.yW aw B.vz B.vx B.vy
      xa an B.xz.symm B.yz.symm B.xy (fun w ww=>gate w ww _ (r _ B.zW))
  let S : Finset V := {tag B.x,tag B.y,tag B.z}
  have card : S.card=3 := by simp [S,txy,txz,tyz]
  have sub : S⊆A := by
    intro c cm
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at cm
    rcases cm with rfl|rfl|rfl
    · exact r _ B.xW
    · exact r _ B.yW
    · exact r _ B.zW
  refine ⟨S,sub,card,?_⟩
  intro c cm
  simp only [S,Finset.mem_insert,Finset.mem_singleton] at cm
  rcases cm with rfl|rfl|rfl
  · exact ax
  · exact ay
  · exact az

theorem P9_of_two_three_color_arm_families {X Y : Set V} (A S T : Finset V)
    (small : A.card≤5) (sa : S⊆A) (ta : T⊆A) (s3 : S.card=3) (t3 : T.card=3)
    (offX : ∀ x∈X,x∉A) (offY : ∀ y∈Y,y∉A)
    (dis : Disjoint X Y) (anti : ∀ x∈X,∀ y∈Y,¬G.Adj x y)
    (sx : ∀ a∈S,Arm (G:=G) X a) (ty : ∀ b∈T,Arm (G:=G) Y b) :
    ∃ f : Fin 9→V,InducedPath G f := by
  classical
  have dj : ¬Disjoint S T := by
    intro no
    have h := Finset.card_le_card (Finset.union_subset sa ta)
    rw [Finset.card_union_of_disjoint no,s3,t3] at h
    omega
  obtain ⟨g,gm⟩ := Finset.not_disjoint_iff_nonempty_inter.mp dj
  obtain ⟨gs,gt⟩ := Finset.mem_inter.mp gm
  exact two_clean_arms_induced_P9 (fun gx=>offX g gx (sa gs)) (fun gy=>offY g gy (sa gs))
    dis anti (sx g gs) (ty g gt)

theorem P9_of_two_outer_branches {X Y : Set V}
    (A : Finset V) (small : A.card≤5) (h4 : FourCycleFree G)
    (tag : V→V) (range : ∀ x∈X∪Y,tag x∈A) (off : ∀ x∈X∪Y,x∉A)
    (tri : ∀ a∈X∪Y,∀ b∈X∪Y,∀ c∈X∪Y,G.Adj a b→G.Adj b c→¬G.Adj a c)
    (proper : ∀ a∈X∪Y,∀ b∈X∪Y,G.Adj a b→tag a≠tag b)
    (gate : ∀ x∈X∪Y,∀ a∈A,G.Adj a x↔tag x=a)
    (dis : Disjoint X Y) (anti : ∀ x∈X,∀ y∈Y,¬G.Adj x y)
    (BX : Branch G X) (BY : Branch G Y) :
    ∃ f : Fin 9→V,InducedPath G f := by
  have lx : X⊆X∪Y := Set.subset_union_left
  have ly : Y⊆X∪Y := Set.subset_union_right
  obtain ⟨S,sa,s3,rs⟩ := three_arm_colors_of_branch A h4 tag
    (fun x xm=>range x (lx xm)) (fun x xm=>off x (lx xm))
    (fun a am b bm c cm=>tri a (lx am) b (lx bm) c (lx cm))
    (fun a am b bm=>proper a (lx am) b (lx bm)) (fun x xm=>gate x (lx xm)) BX
  obtain ⟨T,ta,t3,rt⟩ := three_arm_colors_of_branch A h4 tag
    (fun x xm=>range x (ly xm)) (fun x xm=>off x (ly xm))
    (fun a am b bm c cm=>tri a (ly am) b (ly bm) c (ly cm))
    (fun a am b bm=>proper a (ly am) b (ly bm)) (fun x xm=>gate x (ly xm)) BY
  exact P9_of_two_three_color_arm_families A S T small sa ta s3 t3
    (fun x xm=>off x (lx xm)) (fun y ym=>off y (ly ym)) dis anti rs rt

#print axioms P9_of_two_outer_branches
#print axioms three_arm_colors_of_branch
#print axioms P9_of_two_three_color_arm_families
#print axioms two_clean_arms_induced_P9
#print axioms arm_from_branch_neighbor
end Graffiti133NestedFour
