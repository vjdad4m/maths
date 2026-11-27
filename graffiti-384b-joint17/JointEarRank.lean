import JointEarSample
namespace Graffiti384b.Joint17
open Finset SimpleGraph
open private Repair.nbr_add from Repair384b
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem transpose (X F : Finset V) : (∑ v∈X,nbr G v F)=∑ i∈F,nbr G i X := by
  calc _ = ∑ v∈X,∑ i∈F,if G.Adj v i then 1 else 0 := by simp [nbr,sum_boole]
       _ = ∑ i∈F,∑ v∈X,if G.Adj i v then 1 else 0 := by rw [sum_comm]; simp_rw [G.adj_comm]
       _ = _ := by simp [nbr,sum_boole]

/-- Joint obstruction for three independent ears with high anchors. The
two other ears have four incidences in total. Every incidence missing the
high sampling pool adds an explicit charge. -/
theorem independent_budget (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (bad : bound G<gamma G)
    (ha : 3≤G.degree a) (hb : 3≤G.degree b)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v) :
    let A : Finset V := {a,b}
    let X := high G\A
    let F := (LowSample.twos G).erase e
    let Z := W\(X∪F)
    let hits := fun v => 0<nbr G v A
    629850*(W.filter hits).card+405536*(4-∑ v∈F,nbr G v X)+629850*(1-(Z.filter hits).card) ≤ 10349034 := by
  classical
  let A : Finset V := {a,b}
  let X := high G\A
  let E := LowSample.twos G
  let F := E.erase e
  let Z := W\(X∪F)
  let hits := fun v => 0<nbr G v A
  let mark := fun v => if hits v then 1 else 0
  let bns := fun v => (27-nbr G v X).choose (9-nbr G v X)
  let c := 4-∑ i∈F,nbr G i X
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have ws : W.card=30 := by rw [wdef,card_compl,card_insert_of_not_mem (by simp [ea.ne,eb.ne]),card_pair ab,n]
  obtain ⟨hs,es⟩ := Cover31.residual G t q bad
  have ah : A⊆high G := insert_subset (mem_filter.mpr ⟨mem_univ _,ha⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_univ _,hb⟩))
  have xs : X.card=27 := by dsimp [X]; rw [card_sdiff ah,hs,show A.card=2 from card_pair ab]
  have two (v : V) (vm : v∈E) : G.degree v=2 := by
    obtain ⟨nl,nh⟩ := mem_sdiff.mp vm
    have lo := (mem_filter.mp nl).2
    have hi : ¬3≤G.degree v := fun h => nh (mem_filter.mpr ⟨mem_univ _,h⟩)
    omega
  have em : e∈E := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have fs : F.card=2 := by dsimp [F,E]; rw [card_erase_of_mem em,es]
  have xe : Disjoint X E := disjoint_left.mpr (fun _ m ex => (mem_sdiff.mp ex).2 (mem_sdiff.mp m).1)
  have xf := xe.mono_right (show F⊆E from erase_subset ..)
  have ax : Disjoint A X := disjoint_left.mpr (fun _ m x => (mem_sdiff.mp x).2 m)
  have af : Disjoint A F := disjoint_left.mpr (fun _ m f => (mem_sdiff.mp (mem_erase.mp f).2).2 (ah m))
  have xw : X⊆W := by
    intro v vm; rw [wdef]; apply mem_compl.mpr; intro m
    rcases mem_insert.mp m with rfl|va
    · exact disjoint_left.mp xe vm em
    · exact (mem_sdiff.mp vm).2 va
  have fw : F⊆W := by
    intro v vm; rw [wdef]; apply mem_compl.mpr; intro m
    exact (mem_insert.mp m).elim (mem_erase.mp vm).1 (fun va => disjoint_left.mp af va vm)
  have both : X∪F⊆W := union_subset xw fw
  have zs : Z.card=1 := by dsimp [Z]; rw [card_sdiff both,card_union_of_disjoint xf,ws,xs,fs]
  have zbound := card_le_card (filter_subset hits Z)
  have ca (v : V) (vm : v∈X) : nbr G v A≤1 := (PortRepair29.thin_degrees G ear thin v (wdef ▸ xw vm)).1
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have boundRank := ranked G X A F xs (disjoint_union_left.mpr ⟨ax,xf.symm⟩) af ca fs
    (inj.mono (show (X:Set V)⊆high G from sdiff_subset)) (fun v vm => floor v (mem_sdiff.mp vm).1)
  have mass := ear_mass G X E xs xe (fun u um v vm => ind u v (two u um) (two v vm)) two n
    (by rw [bound,n,t] at bad; omega)
  have neX : nbr G e X=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro v vm; obtain ⟨vx,ev⟩ := mem_filter.mp vm
    exact (mem_sdiff.mp vx).2 (show v∈({a,b}:Finset V) from ear ▸ (G.mem_neighborFinset ..).mpr ev)))
  have bn : bns e=4686825 := by dsimp [bns]; rw [neX,Nat.choose_eq_fast_choose]; decide
  have part := sum_erase_add E bns em
  change (∑ i∈F,bns i)+bns e=∑ i∈E,bns i at part
  rw [bn] at part
  change 3*4686825+(∑ v∈E,bns v)≤_ at mass
  have fx (v : V) (m : v∈F) : nbr G v X+nbr G v A≤2 := by
    rw [←Repair.nbr_add G v ax.symm,←two v (mem_erase.mp m).2,←card_neighborFinset_eq_degree]
    exact card_le_card (fun i im => (G.mem_neighborFinset ..).mpr (mem_filter.mp im).2)
  have numeric : ∀ j : Fin 3,480700+1081575*(2-j.val)≤(27-j.val).choose (9-j.val) := by
    simp only [Nat.choose_eq_fast_choose]; decide
  have count := sum_le_sum (s:=F) (fun v vm => show nbr G v X≤2 by have := fx v vm; omega)
  simp only [sum_const,smul_eq_mul,fs] at count
  have bnd (v : V) (m : v∈F) : 480700+1081575*2≤bns v+1081575*nbr G v X := by
    have low := fx v m
    have z := numeric ⟨nbr G v X,by omega⟩
    change 480700+1081575*(2-nbr G v X)≤bns v at z; omega
  have bnTot := sum_le_sum bnd
  simp only [sum_const,smul_eq_mul,fs,sum_add_distrib,←mul_sum] at bnTot
  have xm (v : V) (_ : v∈X) : mark v≤nbr G v A := by dsimp [mark,hits]; split <;> omega
  have fm (v : V) (vm : v∈F) : mark v+nbr G v X≤2 := by
    have z := fx v vm; dsimp [mark,hits]; split <;> omega
  have xmTot := sum_le_sum xm
  have fmTot := sum_le_sum fm
  simp only [sum_add_distrib,sum_const,smul_eq_mul,fs] at fmTot
  have spl := sum_sdiff both (f:=mark)
  rw [sum_union xf] at spl
  change (∑ v∈Z,mark v)+((∑ v∈X,mark v)+∑ v∈F,mark v)=∑ v∈W,mark v at spl
  have marks (S : Finset V) : (∑ v∈S,mark v)=(S.filter hits).card := by
    dsimp only [mark]; rw [←sum_filter]; simp
  rw [marks Z,marks W] at spl
  rw [transpose G X F] at boundRank
  change 629850*(W.filter hits).card+405536*(4-∑ v∈F,nbr G v X)+629850*(1-(Z.filter hits).card)≤10349034
  omega

/-- Every thin ear in this frontier has at most sixteen exterior contacts. -/
theorem contact_cap (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (bad : bound G<gamma G) :
    (W.filter (fun v => 0<nbr G v {a,b})).card≤16 := by
  by_contra! hits
  obtain ⟨ha,hb,ind⟩ := Weighted29.independent_at_seventeen G n q t ear ab thin W wdef bad (by omega)
  have z := independent_budget G n q t ear ab thin W wdef bad ha hb ind
  dsimp only at z
  omega

/-- At sixteen contacts in the independent case, all four remaining
incidences land on high vertices outside the fixed pair, and a leaf
sees the fixed pair. -/
theorem independent_sixteen (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (bad : bound G<gamma G)
    (hits : 16≤(W.filter (fun v => 0<nbr G v {a,b})).card)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v) :
    (∀ v,G.degree v=2 → v≠e → G.neighborFinset v⊆high G\{a,b}) ∧
    ∃ z∈W,G.degree z=1 ∧ 0<nbr G z {a,b} := by
  classical
  let A : Finset V := {a,b}
  let X := high G\A
  let F := (LowSample.twos G).erase e
  let Z := W\(X∪F)
  let hit := fun v => 0<nbr G v A
  have lo := (Weighted29.low_anchors G n q t ear ab thin W wdef bad).1
  have ha : 3≤G.degree a := by by_contra! h; have := lo (Or.inl (by omega)); omega
  have hb : 3≤G.degree b := by by_contra! h; have := lo (Or.inr (by omega)); omega
  have bound' := independent_budget G n q t ear ab thin W wdef bad ha hb ind
  change 629850*(W.filter hit).card+405536*(4-∑ v∈F,nbr G v X)+629850*(1-(Z.filter hit).card)≤10349034 at bound'
  change 16≤(W.filter hit).card at hits
  have full : 4≤∑ v∈F,nbr G v X := by omega
  have someHit : 0<(Z.filter hit).card := by omega
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have memTwo {v : V} (d : G.degree v=2) : v∈LowSample.twos G := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have fs : F.card=2 := by dsimp [F]; rw [card_erase_of_mem (memTwo de),(Cover31.residual G t q bad).2]
  have small (i : V) (m : i∈F) : nbr G i X≤2 := by
    have ih := (mem_sdiff.mp (mem_erase.mp m).2).2
    have di : G.degree i≤2 := by by_contra! z; exact ih (mem_filter.mpr ⟨mem_univ _,z⟩)
    exact (card_le_card (show X.filter (G.Adj i)⊆G.neighborFinset i from
      fun _ wm => (G.mem_neighborFinset ..).mpr (mem_filter.mp wm).2)).trans ((card_neighborFinset_eq_degree ..).le.trans di)
  constructor
  · intro v dv ve
    have vm : v∈F := mem_erase.mpr ⟨ve,memTwo dv⟩
    have part := sum_erase_add F (fun i => nbr G i X) vm
    change (∑ i∈F.erase v,nbr G i X)+nbr G v X=∑ i∈F,nbr G i X at part
    have rest := sum_le_sum (s:=F.erase v) (fun i im => small i (mem_erase.mp im).2)
    rw [sum_const,card_erase_of_mem vm,fs] at rest
    have eq : X.filter (G.Adj v)=G.neighborFinset v := by
      apply eq_of_subset_of_card_le (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
      rw [card_neighborFinset_eq_degree,dv]; change 2≤nbr G v X
      norm_num at rest; omega
    exact eq ▸ filter_subset .. 
  · obtain ⟨z,zm⟩ := card_pos.mp someHit
    obtain ⟨zZ,credit⟩ := mem_filter.mp zm
    obtain ⟨zw,off⟩ := mem_sdiff.mp zZ
    have za : z∉A := fun m => mem_compl.mp (wdef ▸ zw) (mem_insert_of_mem m)
    have ze : z≠e := fun eq => mem_compl.mp (wdef ▸ zw) (eq ▸ mem_insert_self ..)
    have nh : z∉high G := fun zh => off (mem_union_left F (mem_sdiff.mpr ⟨zh,za⟩))
    have nt : G.degree z≠2 := fun d => off (mem_union_right X (mem_erase.mpr ⟨ze,memTwo d⟩))
    have notHigh : ¬3≤G.degree z := fun d => nh (mem_filter.mpr ⟨mem_univ _,d⟩)
    have pd := card_le_card (show A.filter (G.Adj z)⊆G.neighborFinset z from fun _ m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    rw [card_neighborFinset_eq_degree] at pd
    change nbr G z A≤G.degree z at pd
    change 0<nbr G z A at credit
    exact ⟨z,zw,by omega,credit⟩

/-- The catalogue inequality holds in the entire seventeen-contact case. -/
theorem exact_of_seventeen (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e})
    (h : 17≤(((insert e ({a,b}:Finset V))ᶜ).filter (fun v => 0<nbr G v {a,b})).card) : gamma G≤bound G := by
  by_contra! bad
  have z := contact_cap G n q t ear ab thin _ rfl bad
  omega

end Graffiti384b.Joint17
#print axioms Graffiti384b.Joint17.independent_budget
#print axioms Graffiti384b.Joint17.contact_cap
#print axioms Graffiti384b.Joint17.independent_sixteen
#print axioms Graffiti384b.Joint17.exact_of_seventeen
