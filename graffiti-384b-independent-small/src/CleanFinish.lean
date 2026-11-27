import CleanRanks
import FinishIndependent
namespace Graffiti384b.Clean
open Finset SimpleGraph Simplicial16 Reserved16
open private Joint17.transpose from JointEarRank
open private FiniteRange.bad from FiniteRange384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 2500000 in
/-- Every independent-ear graph in the order-33 profile with high anchors
and all four other-ear incidences in the high exterior satisfies the bound. -/
theorem exact_clean (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e})
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    (anchors : ({a,b}:Finset V)⊆high G)
    (other : ∀ v,G.degree v=2 → v≠e → G.neighborFinset v⊆high G\{a,b}) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  let A : Finset V := {a,b}
  let W := (insert e A)ᶜ
  let X := high G\A
  let E := LowSample.twos G
  let F := E.erase e
  let Z := W\(X∪F)
  let hit := fun v => 0<nbr G v A
  let bn := fun v => (27-nbr G v X).choose (10-nbr G v X)
  have ah : A⊆high G := anchors
  have hh : (W.filter hit).card≤10 := by
    by_contra! large
    exact (not_lt_of_ge (IndependentEleven.exact_of_eleven G n q t ear ab thin ind large)) bad
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have ws : W.card=30 := by dsimp [W,A]; rw [card_compl,card_insert_of_not_mem (by simp [ea.ne,eb.ne]),card_pair ab,n]
  obtain ⟨hs,es⟩ := Cover31.residual G t q bad
  have xs : X.card=27 := by dsimp [X]; rw [card_sdiff ah,hs,show A.card=2 from card_pair ab]
  have mE {v : V} (d : G.degree v=2) : v∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have two (v : V) (m : v∈E) : G.degree v=2 := by
    obtain ⟨nl,nh⟩ := mem_sdiff.mp m
    have lower := (mem_filter.mp nl).2
    have upper := Nat.le_of_not_gt (fun h : 2<G.degree v => nh (mem_filter.mpr ⟨mem_univ _,h⟩))
    omega
  have fs : F.card=2 := by dsimp [F,E]; rw [card_erase_of_mem (mE de),es]
  have xe : Disjoint X E := disjoint_left.mpr (fun _ m z => (mem_sdiff.mp z).2 (mem_sdiff.mp m).1)
  have xf := xe.mono_right (show F⊆E from erase_subset ..)
  have ax : Disjoint A X := disjoint_left.mpr (fun _ m x => (mem_sdiff.mp x).2 m)
  have af : Disjoint A F := disjoint_left.mpr (fun _ m f => (mem_sdiff.mp (mem_erase.mp f).2).2 (ah m))
  have xw : X⊆W := by
    intro v vm; apply mem_compl.mpr; intro m
    rcases mem_insert.mp m with rfl|va
    · exact disjoint_left.mp xe vm (mE de)
    · exact (mem_sdiff.mp vm).2 va
  have fw : F⊆W := by
    intro v vm; apply mem_compl.mpr; intro m
    exact (mem_insert.mp m).elim (mem_erase.mp vm).1 (fun va => disjoint_left.mp af va vm)
  have both : X∪F⊆W := union_subset xw fw
  have zs : Z.card=1 := by dsimp [Z]; rw [card_sdiff both,card_union_of_disjoint xf,ws,xs,fs]
  have all (v : V) (m : v∈F) : G.neighborFinset v⊆X := other v (two v (mem_erase.mp m).2) (mem_erase.mp m).1
  have ca (v : V) (vm : v∈X) : nbr G v A≤1 := (PortRepair29.thin_degrees G ear thin v (xw vm)).1
  have fzero (i : V) (m : i∈F) : nbr G i A=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro y ym
    obtain ⟨ya,iy⟩ := mem_filter.mp ym
    exact disjoint_left.mp ax ya (all i m ((G.mem_neighborFinset ..).mpr iy))))
  have fx (v : V) (vm : v∈F) : nbr G v X=2 := by
    have eq : X.filter (G.Adj v)=G.neighborFinset v := by
      ext y; simp only [mem_filter,mem_neighborFinset]; exact ⟨And.right,fun vy => ⟨all v vm ((G.mem_neighborFinset ..).mpr vy),vy⟩⟩
    rw [nbr,eq,card_neighborFinset_eq_degree,two v (mem_erase.mp vm).2]
  have fsum : (∑ v∈F,nbr G v X)=4 := by
    calc _ = ∑ _v∈F,2 := sum_congr rfl fx
         _ = 4 := by simp [fs]
  have pos : (Z.filter hit).card≤1 := (card_le_card (filter_subset hit Z)).trans zs.le
  have split := sum_sdiff both (f:=fun v => if hit v then (1:ℕ) else 0)
  rw [sum_union xf] at split
  have marks (S : Finset V) : (∑ v∈S,if hit v then 1 else 0)=(S.filter hit).card := by rw [←sum_filter]; simp
  change (∑ v∈Z,if hit v then 1 else 0)+((∑ v∈X,if hit v then 1 else 0)+∑ v∈F,if hit v then 1 else 0)=∑ v∈W,if hit v then 1 else 0 at split
  have none : F.filter hit=∅ := eq_empty_of_forall_not_mem (by intro i m; have v := (mem_filter.mp m).2; change 0<nbr G i A at v; rw [fzero i (mem_filter.mp m).1] at v; omega)
  rw [marks Z,marks F,marks W,none,card_empty] at split
  have mask : (∑ v∈X,nbr G v A)+(Z.filter hit).card=(W.filter hit).card := by
    have rows (v : V) (m : v∈X) : nbr G v A=(if hit v then 1 else 0) := by have := ca v m; dsimp [hit]; split <;> omega
    rw [sum_congr rfl rows]; omega
  have pairs := Joint17.transpose G X A
  rw [show (∑ v∈A,nbr G v X)=nbr G a X+nbr G b X by simp [A,ab]] at pairs
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have av : a∈A := mem_insert_self ..
  have bv : b∈A := mem_insert_of_mem (mem_singleton_self _)
  have xh : X⊆high G := sdiff_subset
  have injX := inj.mono (show (X:Set V)⊆high G from xh)
  have exclude (v : V) (vm : v∈X) : trianglesAt G v≠trianglesAt G a ∧ trianglesAt G v≠trianglesAt G b :=
    ⟨fun eq => disjoint_left.mp ax av (inj (xh vm) (ah av) eq ▸ vm),
     fun eq => disjoint_left.mp ax bv (inj (xh vm) (ah bv) eq ▸ vm)⟩
  have zero : nbr G e X=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro v vm; obtain ⟨vx,ev⟩ := mem_filter.mp vm; exact disjoint_left.mp ax (show v∈({a,b}:Finset V) from ear ▸ (G.mem_neighborFinset ..).mpr ev) vx))
  have part := sum_erase_add E bn (mE de)
  change (∑ v∈F,bn v)+bn e=∑ v∈E,bn v at part
  have earBonus : bn e=8436285 := by dsimp [bn]; rw [zero,Nat.choose_eq_fast_choose]; decide
  have second : (∑ v∈F,bn v)=2*1081575 := by
    calc _ = ∑ _v∈F,1081575 := sum_congr rfl (fun v vm => by dsimp [bn]; rw [fx v vm,Nat.choose_eq_fast_choose]; decide)
         _ = _ := by simp [fs]
  rw [second,earBonus] at part
  have bs := anchor_score G ear thin X rfl other
  have as' := anchor_score G (ear.trans (pair_comm ..)) ((inter_comm ..).trans thin) X (by dsimp [X,A]; rw [pair_comm a b]) other
  have outsideX (w : V) (out : w∉X) : trianglesAt G w≤max (trianglesAt G a) (trianglesAt G b) := by
    by_cases wh : w∈high G
    · have inA : w∈A := by by_contra wa; exact out (mem_sdiff.mpr ⟨wh,wa⟩)
      rcases mem_insert.mp inA with rfl|wb
      · exact le_max_left ..
      · rw [mem_singleton.mp wb]; exact le_max_right ..
    · have low : G.degree w≤2 := Nat.le_of_lt_succ (by simpa [high] using wh)
      have bound' := (Repair.triangles_le_choose G w).trans (Nat.choose_le_choose 2 low)
      have low' := floor a (ah av)
      have mx := Nat.le_max_left (trianglesAt G a) (trianglesAt G b)
      have one : (2:ℕ).choose 2=1 := by decide
      omega
  let x := nbr G a X
  let y := nbr G b X
  let u := min x y
  let w := max x y
  have sumxy : x+y=∑ v∈X,nbr G v A := pairs.symm
  have sg : u+w=x+y := by
    dsimp only [u,w]
    rcases le_total x y with le|le
    · rw [min_eq_left le,max_eq_right le]
    · rw [min_eq_right le,max_eq_left le,Nat.add_comm]
  have lx {z p : ℕ} (lo : 2≤p) (cap : p≤1+z.choose 2) : 2≤z := by
    by_contra! no
    have z1 : z≤1 := by omega
    have zz := Nat.choose_le_choose 2 z1
    rw [show (1:ℕ).choose 2=0 by decide] at zz; omega
  have ax2 : 2≤x := lx (floor a (ah av)) as'
  have by2 : 2≤y := lx (floor b (ah bv)) bs
  have u2 : 2≤u := le_min ax2 by2
  have uw : u≤w := (min_le_left x y).trans (le_max_left x y)
  have five : 5≤u+w := by
    by_contra! no
    have xx : nbr G a X=2 := by change x=2; omega
    have yy : nbr G b X=2 := by change y=2; omega
    rw [xx,show (2:ℕ).choose 2=1 by decide] at as'
    rw [yy,show (2:ℕ).choose 2=1 by decide] at bs
    have la := floor a (ah av)
    have lb := floor b (ah bv)
    exact ab (inj (ah av) (ah bv) (by omega))
  have ten : u+w≤10 := by omega
  obtain ⟨m,um,wm⟩ := coverage ⟨u,by omega⟩ ⟨w,by omega⟩ u2 uw five ten
  change leftSize m=u at um
  change rightSize m=w at wm
  have sm : trianglesAt G a≤1+(leftSize m).choose 2 ∨ trianglesAt G b≤1+(leftSize m).choose 2 := by
    rw [um]; rcases le_total x y with le|le
    · rw [show u=x from min_eq_left le]; exact Or.inl as'
    · rw [show u=y from min_eq_right le]; exact Or.inr bs
  have big : max (trianglesAt G a) (trianglesAt G b)≤1+(rightSize m).choose 2 := by
    rw [wm]; apply max_le
    · exact as'.trans (Nat.add_le_add_left (Nat.choose_le_choose 2 (le_max_left x y)) 1)
    · exact bs.trans (Nat.add_le_add_left (Nat.choose_le_choose 2 (le_max_right x y)) 1)
  have clean (v : V) (vm : v∈X) (no : nbr G v F=0) : nbr G v E=0 := by
    have notNear : ¬G.Adj v e := fun edge => disjoint_left.mp ax
      (show v∈({a,b}:Finset V) from ear ▸ (G.mem_neighborFinset ..).mpr edge.symm) vm
    have eq : E.filter (G.Adj v)=F.filter (G.Adj v) := by
      ext w; simp only [F,mem_filter,mem_erase]
      constructor
      · rintro ⟨wm,vw⟩; exact ⟨⟨fun h => notNear (h ▸ vw),wm⟩,vw⟩
      · exact fun h => ⟨h.1.2,h.2⟩
    simpa only [nbr,eq] using (show (F.filter (G.Adj v)).card=0 from no)
  have rank := ranked G X A F E xs (disjoint_union_left.mpr ⟨ax,xf.symm⟩) xh af ca fs injX (fun v m => floor v (xh m))
    _ _ (floor a (ah av)) (floor b (ah bv)) (fun eq => ab (inj (ah av) (ah bv) eq)) exclude m sm big outsideX clean
  rw [um,wm,sg,sumxy,Joint17.transpose G X F,fsum] at rank
  have cubic := Eleven.extra_mass G 9 (by decide) (by decide) X E xs xe
    (fun u um v vm => ind u v (two u um) (two v vm)) two xh injX n (by rw [bound,n,t] at bad; omega)
  change 2*(27:ℕ).choose 10+(∑ v∈E,bn v)+_+_≤_ at cubic
  rw [show (27:ℕ).choose 10=8436285 by rw [Nat.choose_eq_fast_choose]; decide] at cubic
  simp only [show (9:ℕ)+1=10 from rfl] at cubic
  omega

/-- An independent-ear failure has an ear attached to a leaf, or two
different ears sharing a neighbor. The ear with a unique common
neighbor is supplied by the earlier three-square reduction. -/
theorem leaf_or_shared (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v) (bad : bound G<gamma G) :
    (∃ u v,G.degree u=2 ∧ G.degree v=1 ∧ G.Adj u v) ∨
    ∃ u v w,u≠v ∧ G.degree u=2 ∧ G.degree v=2 ∧ G.neighborFinset u∩G.neighborFinset v={w} := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨e,a,b,de,ab,ear,thin⟩ := Squares29.thin_at_32 G t q bad
  have highNbr {u w : V} (du : G.degree u=2) (uw : G.Adj u w) : w∈high G := by
    apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
    have ne2 : G.degree w≠2 := fun dw => ind u w du dw uw
    have ne1 : G.degree w≠1 := fun dw => no (Or.inl ⟨u,w,du,dw,uw⟩)
    have pos : 0<(G.neighborFinset w).card := card_pos.mpr ⟨u,(G.mem_neighborFinset ..).mpr uw.symm⟩
    rw [card_neighborFinset_eq_degree] at pos; omega
  have anchors : ({a,b}:Finset V)⊆high G := by
    rw [←ear]; intro w wm; exact highNbr de ((G.mem_neighborFinset ..).mp wm)
  have other (u : V) (du : G.degree u=2) (ue : u≠e) : G.neighborFinset u⊆high G\{a,b} := by
    intro w wm
    have uw := (G.mem_neighborFinset ..).mp wm
    refine mem_sdiff.mpr ⟨highNbr du uw,?_⟩
    intro wa; rw [←ear] at wa
    have one : G.neighborFinset u∩G.neighborFinset e={w} := by
      ext i
      simp only [mem_inter,mem_singleton]
      constructor
      · rintro ⟨iu,ie⟩
        by_cases same : i=w
        · exact same
        · have pairCard : ({i,w}:Finset V).card=2 := card_pair same
          have eqU : ({i,w}:Finset V)=G.neighborFinset u :=
            eq_of_subset_of_card_le (insert_subset iu (singleton_subset_iff.mpr wm)) (by rw [pairCard,card_neighborFinset_eq_degree,du])
          have eqE : ({i,w}:Finset V)=G.neighborFinset e :=
            eq_of_subset_of_card_le (insert_subset ie (singleton_subset_iff.mpr wa)) (by rw [pairCard,card_neighborFinset_eq_degree,de])
          exact False.elim ((not_lt_of_ge (Repair.exact_of_twin_degree_two G ue du (eqU.symm.trans eqE))) bad)
      · rintro rfl; exact ⟨wm,wa⟩
    exact no (Or.inr ⟨u,e,w,ue,du,de,one⟩)
  exact (not_lt_of_ge (exact_clean G n q t ear ab thin ind anchors other)) bad

end Graffiti384b.Clean
#print axioms Graffiti384b.Clean.exact_clean
#print axioms Graffiti384b.Clean.leaf_or_shared
