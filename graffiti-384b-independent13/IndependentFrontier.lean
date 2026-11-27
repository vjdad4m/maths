import SimplicialRanks
namespace Graffiti384b.Simplicial16
open Finset SimpleGraph
open private Joint17.transpose from JointEarRank
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Joint obstruction for three independent ears with high anchors. The
two other ears have four incidences in total. Every incidence missing the
high sampling pool adds an explicit charge. -/
theorem pool_budget (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (bad : bound G<gamma G)
    (X : Finset V) (pool : X⊆high G\{a,b}) (xs : X.card=27)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v) :
    let A : Finset V := {a,b}
    let F := (LowSample.twos G).erase e
    let Z := W\(X∪F)
    let hits := fun v => 0<nbr G v A
    453492*(W.filter hits).card+581894*(4-∑ v∈F,nbr G v X)+453492*(1-(Z.filter hits).card) ≤ 6312902 := by
  classical
  let A : Finset V := {a,b}
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
  have highX : X⊆high G := pool.trans sdiff_subset
  have two (v : V) (vm : v∈E) : G.degree v=2 := by
    obtain ⟨nl,nh⟩ := mem_sdiff.mp vm
    have lo := (mem_filter.mp nl).2
    have hi : ¬3≤G.degree v := fun h => nh (mem_filter.mpr ⟨mem_univ _,h⟩)
    omega
  have em : e∈E := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have fs : F.card=2 := by dsimp [F,E]; rw [card_erase_of_mem em,es]
  have xe : Disjoint X E := disjoint_left.mpr (fun _ m ex => (mem_sdiff.mp ex).2 (mem_sdiff.mp (pool m)).1)
  have xf := xe.mono_right (show F⊆E from erase_subset ..)
  have ax : Disjoint A X := disjoint_left.mpr (fun _ m x => (mem_sdiff.mp (pool x)).2 m)
  have af : Disjoint A F := disjoint_left.mpr (by
    intro v va vf
    exact ind e v de (two v (mem_erase.mp vf).2) ((G.mem_neighborFinset ..).mp (ear.symm ▸ (show v∈({a,b}:Finset V) from va))))
  have xw : X⊆W := by
    intro v vm; rw [wdef]; apply mem_compl.mpr; intro m
    rcases mem_insert.mp m with rfl|va
    · exact disjoint_left.mp xe vm em
    · exact (mem_sdiff.mp (pool vm)).2 va
  have fw : F⊆W := by
    intro v vm; rw [wdef]; apply mem_compl.mpr; intro m
    exact (mem_insert.mp m).elim (mem_erase.mp vm).1 (fun va => disjoint_left.mp af va vm)
  have both : X∪F⊆W := union_subset xw fw
  have zs : Z.card=1 := by dsimp [Z]; rw [card_sdiff both,card_union_of_disjoint xf,ws,xs,fs]
  have zbound := card_le_card (filter_subset hits Z)
  have ca (v : V) (vm : v∈X) : nbr G v A≤1 := (PortRepair29.thin_degrees G ear thin v (wdef ▸ xw vm)).1
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have boundRank := ranked G X A F xs (disjoint_union_left.mpr ⟨ax,xf.symm⟩) highX af ca fs
    (inj.mono (show (X:Set V)⊆high G from highX)) (fun v vm => floor v (highX vm))
  have mass := Simplicial16.mass G X E xs xe (fun u um v vm => ind u v (two u um) (two v vm)) two highX (inj.mono (show (X:Set V)⊆high G from highX)) n
    (by rw [bound,n,t] at bad; omega)
  have neX : nbr G e X=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro v vm; obtain ⟨vx,ev⟩ := mem_filter.mp vm
    exact (mem_sdiff.mp (pool vx)).2 (show v∈({a,b}:Finset V) from ear ▸ (G.mem_neighborFinset ..).mpr ev)))
  have bn : bns e=4686825 := by dsimp [bns]; rw [neX,Nat.choose_eq_fast_choose]; decide
  have part := sum_erase_add E bns em
  change (∑ i∈F,bns i)+bns e=∑ i∈E,bns i at part
  rw [bn] at part
  change 3*4686825+(∑ v∈E,bns v)+(∑ v∈X,((X.powersetCard 9).filter (fun s => v∈activated G X s)).card)≤_ at mass
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
  rw [Joint17.transpose G X F] at boundRank
  change 453492*(W.filter hits).card+581894*(4-∑ v∈F,nbr G v X)+453492*(1-(Z.filter hits).card)≤6312902
  omega

/-- No independent three-ear failure at fourteen or more exterior contacts,
including when one of the two fixed neighbors is a leaf. -/
theorem exact_of_fourteen (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e})
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    (contacts : 14≤(((insert e ({a,b}:Finset V))ᶜ).filter (fun v => 0<nbr G v {a,b})).card) :
    gamma G≤bound G := by
  by_contra! bad
  have h := (Cover31.residual G t q bad).1
  have available := le_card_sdiff ({a,b}:Finset V) (high G)
  rw [card_pair ab,h] at available
  obtain ⟨X,pool,xs⟩ := exists_subset_card_eq (show 27≤((high G)\{a,b}).card by omega)
  have z := pool_budget G n q t ear ab thin _ rfl bad X pool xs ind
  dsimp only at z; omega

/-- At thirteen contacts every eligible 27-vertex pool contains all four
remaining ear incidences; its single residual vertex is credited. -/
theorem all_pools (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (bad : bound G<gamma G)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    (contacts : 13≤(W.filter (fun v => 0<nbr G v {a,b})).card)
    (X : Finset V) (pool : X⊆high G\{a,b}) (xs : X.card=27) :
    let F := (LowSample.twos G).erase e
    (∀ v∈F,G.neighborFinset v⊆X) ∧ ∃ z∈W\(X∪F),0<nbr G z {a,b} := by
  classical
  let F := (LowSample.twos G).erase e
  let Z := W\(X∪F)
  let h := fun v => 0<nbr G v {a,b}
  have z := pool_budget G n q t ear ab thin W wdef bad X pool xs ind
  change 453492*(W.filter h).card+581894*(4-∑ i∈F,nbr G i X)+453492*(1-(Z.filter h).card)≤6312902 at z
  change 13≤(W.filter h).card at contacts
  have full : 4≤∑ i∈F,nbr G i X := by omega
  have hit : 0<(Z.filter h).card := by omega
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have em : e∈LowSample.twos G := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,
    fun h => by have := (mem_filter.mp h).2; omega⟩
  have fs : F.card=2 := by dsimp [F]; rw [card_erase_of_mem em,(Cover31.residual G t q bad).2]
  have cap (i : V) (m : i∈F) : G.degree i≤2 := by
    have off := (mem_sdiff.mp (mem_erase.mp m).2).2
    exact Nat.le_of_not_gt (fun d => off (mem_filter.mpr ⟨mem_univ _,d⟩))
  have inc (i : V) : X.filter (G.Adj i)⊆G.neighborFinset i := fun _ m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2
  constructor
  · intro v vm
    have part := sum_erase_add F (fun i => nbr G i X) vm
    change (∑ i∈F.erase v,nbr G i X)+nbr G v X=∑ i∈F,nbr G i X at part
    have rest := sum_le_sum (s:=F.erase v) (fun i im => (card_le_card (inc i)).trans
      ((card_neighborFinset_eq_degree ..).le.trans (cap i (mem_erase.mp im).2)))
    change (∑ i∈F.erase v,nbr G i X)≤∑ _i∈F.erase v,2 at rest
    rw [sum_const,card_erase_of_mem vm,fs] at rest
    have eq : X.filter (G.Adj v)=G.neighborFinset v := by
      apply eq_of_subset_of_card_le (inc v); rw [card_neighborFinset_eq_degree]
      change G.degree v≤nbr G v X; have := cap v vm; norm_num at rest; omega
    exact eq ▸ filter_subset ..
  · obtain ⟨z,zm⟩ := card_pos.mp hit
    exact ⟨z,mem_filter.mp zm⟩

/-- In a hypothetical thirteen-contact failure both fixed neighbors are
high. Otherwise an anchor of an exterior ear can be left out of a pool. -/
theorem high_anchors (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (bad : bound G<gamma G)
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    (contacts : 13≤(W.filter (fun v => 0<nbr G v {a,b})).card) : ({a,b}:Finset V)⊆high G := by
  classical
  let A : Finset V := {a,b}
  let H := high G\A
  let E := (LowSample.twos G).erase e
  obtain ⟨hs,es⟩ := Cover31.residual G t q bad
  have al := le_card_sdiff A (high G)
  rw [hs] at al
  change 29-A.card≤H.card at al
  have sz : A.card=2 := card_pair ab
  obtain ⟨X,xh,xs⟩ := exists_subset_card_eq (show 27≤H.card by omega)
  have limits := all_pools G n q t ear ab thin W wdef bad ind contacts
  have en : 2≤E.card := by
    by_cases m : e∈LowSample.twos G
    · dsimp [E]; rw [card_erase_of_mem m,es]
    · dsimp [E]; rw [erase_eq_of_not_mem m,es]; decide
  obtain ⟨f,fm⟩ := card_pos.mp (show 0<E.card by omega)
  have df := (mem_filter.mp (mem_sdiff.mp (mem_erase.mp fm).2).1).2
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(G.neighborFinset f).card by rw [card_neighborFinset_eq_degree]; omega)
  have yx := (limits X xh xs).1 f fm ym
  have size : H.card≤27 := by
    by_contra! large
    have room : 27≤(H.erase y).card := by rw [card_erase_of_mem (xh yx)]; omega
    obtain ⟨Y,ys,yc⟩ := exists_subset_card_eq room
    exact (mem_erase.mp (ys ((limits Y (ys.trans (erase_subset ..)) yc).1 f fm ym))).1 rfl
  have part := card_sdiff_add_card_inter (high G) A
  change H.card+((high G)∩A).card=(high G).card at part
  have eq := eq_of_subset_of_card_le (inter_subset_right : (high G)∩A⊆A) (by omega)
  change A⊆high G
  rw [←eq]; exact inter_subset_left

end Graffiti384b.Simplicial16
#print axioms Graffiti384b.Simplicial16.pool_budget
#print axioms Graffiti384b.Simplicial16.exact_of_fourteen
#print axioms Graffiti384b.Simplicial16.all_pools
#print axioms Graffiti384b.Simplicial16.high_anchors
