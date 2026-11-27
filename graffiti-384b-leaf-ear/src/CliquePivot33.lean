import CoreExtremal33

namespace Graffiti384b.CliquePivot33
open Finset SimpleGraph
open private Repair.isolate Repair.iso_nbr Repair.full_nbr Repair.nbr_mono Repair.triangles_le_choose from Repair384b
open private Prune.links from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A permanently retained outside vertex supplies one neighbor at the roots. -/
def Relaxed (R D : Finset V) : Prop := ∀ v,v∉D → 2≤nbr G v D + (if v∈R then 1 else 0)

def Tight (R : Finset V) : Prop := ∀ D,Relaxed G R D → Fintype.card V≤2*D.card

/-- Omit the pivot with either color. The two candidate dominating sets
partition all vertices except the pivot. -/
theorem shared (R : Finset V) {x : V} {P Q : Finset V} (dis : Disjoint P Q)
    (xp : x∉P) (xq : x∉Q) (px : 2≤nbr G x P) (qx : 2≤nbr G x Q)
    (pinnedP : ∀ v∈P,2≤nbr G v Q) (pinnedQ : ∀ v∈Q,2≤nbr G v P)
    (free : ∀ v,v≠x → v∉P → v∉Q → 3≤(Repair.isolate G x).degree v+2*(if v∈R then 1 else 0)) : ¬Tight G R := by
  intro tight
  let J := Repair.isolate G x
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut J P Q dis
  have pa' : P⊆A.erase x := fun v vp => mem_erase.mpr ⟨fun eq => xp (eq ▸ vp),pa vp⟩
  have qb' : Q⊆Aᶜ.erase x := fun v vq => mem_erase.mpr ⟨fun eq => xq (eq ▸ vq),qb vq⟩
  have first : Relaxed G R (A.erase x) := by
    intro v out
    by_cases vx : v=x
    · subst v; exact Nat.le_add_right_of_le (px.trans (Repair.nbr_mono G _ pa'))
    have va : v∉A := fun h => out (mem_erase.mpr ⟨vx,h⟩)
    by_cases vq : v∈Q
    · exact Nat.le_add_right_of_le ((pinnedQ _ vq).trans (Repair.nbr_mono G _ pa'))
    have deg := free _ vx (fun m => va (pa m)) vq
    have r := rb v (mem_compl.mpr va) vq
    have tot := Repair.full_nbr J v A
    change 3≤J.degree v+2*(if v∈R then 1 else 0) at deg
    rw [← Repair.iso_nbr G vx A]
    change 2≤nbr J v A+(if v∈R then 1 else 0)
    omega
  have second : Relaxed G R (Aᶜ.erase x) := by
    intro v out
    by_cases vx : v=x
    · subst v; exact Nat.le_add_right_of_le (qx.trans (Repair.nbr_mono G _ qb'))
    have va : v∈A := by
      apply Classical.byContradiction; intro m
      exact out (mem_erase.mpr ⟨vx,mem_compl.mpr m⟩)
    by_cases vp : v∈P
    · exact Nat.le_add_right_of_le ((pinnedP _ vp).trans (Repair.nbr_mono G _ qb'))
    have deg := free _ vx vp (fun m => mem_compl.mp (qb m) va)
    have l := la v va vp
    have tot := Repair.full_nbr J v A
    change 3≤J.degree v+2*(if v∈R then 1 else 0) at deg
    rw [← Repair.iso_nbr G vx Aᶜ]
    change 2≤nbr J v Aᶜ+(if v∈R then 1 else 0)
    omega
  have l := tight _ first
  have r := tight _ second
  by_cases xa : x∈A
  · have pos := card_pos.mpr (show A.Nonempty from ⟨x,xa⟩)
    have cap := card_le_univ A
    rw [card_erase_of_mem xa] at l
    rw [erase_eq_of_not_mem (fun m => mem_compl.mp m xa),card_compl] at r
    omega
  · have pos := card_pos.mpr (show Aᶜ.Nonempty from ⟨x,mem_compl.mpr xa⟩)
    rw [card_compl] at pos
    rw [erase_eq_of_not_mem xa] at l
    rw [card_erase_of_mem (mem_compl.mpr xa),card_compl] at r
    omega

private theorem isolated_degree {x v : V} (ne : v≠x) :
    (Repair.isolate G x).degree v=((G.neighborFinset v).erase x).card := by
  rw [← card_neighborFinset_eq_degree]
  congr 1; ext w; simp [Repair.isolate,ne,and_comm]

/-- Pin four clique vertices two on each side. Any exterior cubic affected
by the pivot can be pinned opposite the retained pair when it sees both. -/
theorem paired (R : Finset V) (minimum : ∀ v,2≤G.degree v ∧ (v∉R → 3≤G.degree v))
    {C P : Finset V} {x : V} (cl : G.IsNClique 5 C) (xc : x∈C)
    (pc : P⊆C.erase x) (two : P.card=2)
    (protect : ∀ v,v∉C → G.degree v=3 → G.Adj v x → v∉R → 2≤nbr G v P) : ¬Tight G R := by
  classical
  let Q := C.erase x\P
  let E := (univ : Finset V).filter (fun v => v∉C ∧ G.degree v=3 ∧ G.Adj v x ∧ v∉R)
  have qsize : Q.card=2 := by rw [show Q=C.erase x\P from rfl,card_sdiff pc,card_erase_of_mem xc,cl.2,two]
  have qc : Q⊆C.erase x := sdiff_subset
  have pC := pc.trans (erase_subset _ _)
  have qC := qc.trans (erase_subset _ _)
  have see {v : V} (vc : v∈C) {D : Finset V} (dc : D⊆C) (vd : v∉D) (dz : D.card=2) :
      2≤nbr G v D := by
    have eq : D.filter (G.Adj v)=D := filter_true_of_mem
      (fun w wm => cl.1 vc (dc wm) (fun e => vd (e ▸ wm)))
    simp only [nbr,eq,dz,le_rfl]
  have xp : x∉P := fun m => not_mem_erase _ _ (pc m)
  have xq : x∉Q := fun m => not_mem_erase _ _ (qc m)
  have xe : x∉E := fun m => (mem_filter.mp m).2.1 xc
  have dis : Disjoint P (Q∪E) := disjoint_left.mpr (by
    intro v vm m
    exact (mem_union.mp m).elim (fun h => (mem_sdiff.mp h).2 vm) (fun h => (mem_filter.mp h).2.1 (pC vm)))
  apply shared G R dis xp (fun m => (mem_union.mp m).elim xq xe) (see xc pC xp two)
    ((see xc qC xq qsize).trans (Repair.nbr_mono G _ subset_union_left))
  · intro v vm
    exact (see (pC vm) qC (fun q => (mem_sdiff.mp q).2 vm) qsize).trans (Repair.nbr_mono G _ subset_union_left)
  · intro v vm
    rcases mem_union.mp vm with vq|ve
    · exact see (qC vq) pC (mem_sdiff.mp vq).2 two
    · obtain ⟨vc,d,a,vr⟩ := (mem_filter.mp ve).2
      exact protect _ vc d a vr
  · intro v vx vp vq
    have vc : v∉C := fun m => vq (mem_union_left _ (mem_sdiff.mpr ⟨mem_erase.mpr ⟨vx,m⟩,vp⟩))
    rw [isolated_degree G vx]
    by_cases adj : G.Adj v x
    · rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr adj),card_neighborFinset_eq_degree]
      by_cases vr : v∈R
      · rw [if_pos vr]; have := (minimum v).1; omega
      rw [if_neg vr]
      have not3 : G.degree v≠3 := fun eq => vq (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,vc,eq,adj,vr⟩))
      have := (minimum v).2 vr; omega
    · rw [erase_eq_of_not_mem (fun m => adj ((G.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree]
      by_cases vr : v∈R
      · rw [if_pos vr]; have := (minimum v).1; omega
      · rw [if_neg vr]; have := (minimum v).2 vr; omega

private theorem full_cubic {C : Finset V} (cl : G.IsNClique 5 C) {u : V}
    (du : G.degree u=3) (many : 3≤nbr G u C) :
    G.neighborFinset u⊆C ∧ trianglesAt G u=3 := by
  have same : C.filter (G.Adj u)=G.neighborFinset u := eq_of_subset_of_card_le
    (fun _ m => (G.mem_neighborFinset _ _).mpr (mem_filter.mp m).2) (by rw [card_neighborFinset_eq_degree,du]; exact many)
  have sub : G.neighborFinset u⊆C := same ▸ filter_subset _ _
  have links : Prune.links G u=(G.neighborFinset u).powersetCard 2 := filter_true_of_mem (by
    intro p pm a am b bm ne
    have inc := (mem_powersetCard.mp pm).1
    exact cl.1 (sub (inc am)) (sub (inc bm)) ne)
  refine ⟨sub,?_⟩
  change (Prune.links G u).card=3
  rw [links,card_powersetCard,card_neighborFinset_eq_degree,du]; decide

/-- Each pivot sees an exterior cubic with at most two neighbors in the
clique. Cubics seeing three clique vertices can be protected. -/
theorem cover (R : Finset V) (minimum : ∀ v,2≤G.degree v ∧ (v∉R → 3≤G.degree v))
    (inj : Function.Injective (trianglesAt G)) (extremal : Tight G R)
    {C : Finset V} (cl : G.IsNClique 5 C) {x : V} (xc : x∈C) :
    ∃ v,v∉C ∧ G.degree v=3 ∧ G.Adj v x ∧ v∉R ∧ nbr G v C≤2 := by
  classical
  apply Classical.byContradiction; intro no
  have full (v : V) (vc : v∉C) (dv : G.degree v=3) (adj : G.Adj v x) (vr : v∉R) :
      G.neighborFinset v⊆C ∧ trianglesAt G v=3 := by
    apply full_cubic G cl dv
    have few : ¬nbr G v C≤2 := fun small => no ⟨v,vc,dv,adj,vr,small⟩
    omega
  have enough (P : Finset V) (pc : P⊆C.erase x) (sz : P.card=2)
      (protect : ∀ v,v∉C → G.degree v=3 → G.Adj v x → v∉R → 2≤nbr G v P) : False := by
    exact paired G R minimum cl xc pc sz protect extremal
  by_cases existsV : ∃ u,u∉C ∧ G.degree u=3 ∧ G.Adj u x ∧ u∉R
  · obtain ⟨u,uc,du,ux,ur⟩ := existsV
    obtain ⟨sub,score⟩ := full _ uc du ux ur
    let P := (G.neighborFinset u).erase x
    have pc : P⊆C.erase x := fun v vm => mem_erase.mpr ⟨(mem_erase.mp vm).1,sub (mem_erase.mp vm).2⟩
    have sz : P.card=2 := by rw [show P=(G.neighborFinset u).erase x from rfl,
      card_erase_of_mem ((G.mem_neighborFinset _ _).mpr ux),card_neighborFinset_eq_degree,du]
    apply enough P pc sz
    intro v vc dv vx vr
    have eq : v=u := inj ((full v vc dv vx vr).2.trans score.symm)
    subst v
    have allP : P.filter (G.Adj u)=P := filter_true_of_mem (fun w wm =>
      (G.mem_neighborFinset _ _).mp (erase_subset _ _ wm))
    simp only [nbr,allP,sz,le_rfl]
  · obtain ⟨P,pc,sz⟩ := exists_subset_card_eq (show 2≤(C.erase x).card by rw [card_erase_of_mem xc,cl.2]; decide)
    exact enough P pc sz (fun v vc dv vx vr => (existsV ⟨v,vc,dv,vx,vr⟩).elim)

/-- A positive, cubic-or-higher extremal core must have exactly three cubic
vertices, with triangle counts 1, 2 and 3. They cover every five-clique. -/
theorem three_cubics (R : Finset V) (minimum : ∀ v,2≤G.degree v ∧ (v∉R → 3≤G.degree v))
    (positive : ∀ v,0<trianglesAt G v) (inj : Function.Injective (trianglesAt G)) (extremal : Tight G R)
    {C : Finset V} (cl : G.IsNClique 5 C) :
    let B := univ.filter (fun v => G.degree v=3)
    B.card=3 ∧ B.image (trianglesAt G)=Icc 1 3 ∧
      (∀ v∈B,v∉C ∧ v∉R ∧ nbr G v C≤2) ∧ C⊆B.biUnion (fun v => C.filter (G.Adj v)) := by
  classical
  let B := univ.filter (fun v => G.degree v=3)
  let L := B.filter (fun v => v∉C ∧ v∉R ∧ nbr G v C≤2)
  have covers : C⊆L.biUnion (fun v => C.filter (G.Adj v)) := by
    intro x xc
    obtain ⟨v,vc,d,vx,vr,few⟩ := cover G R minimum inj extremal cl xc
    exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,d⟩,vc,vr,few⟩,mem_filter.mpr ⟨xc,vx⟩⟩
  have cnt : 5≤L.card*2 := calc
    5 = C.card := cl.2.symm
    _ ≤ _ := card_le_card covers
    _ ≤ ∑ v ∈ L,(C.filter (G.Adj v)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ L,2 := Finset.sum_le_sum (fun v vm => (mem_filter.mp vm).2.2.2)
    _ = _ := by simp
  have imageSub : B.image (trianglesAt G)⊆Icc 1 3 := by
    intro j jm
    obtain ⟨v,vm,rfl⟩ := mem_image.mp jm
    have ub := Repair.triangles_le_choose G v
    rw [(mem_filter.mp vm).2] at ub
    exact mem_Icc.mpr ⟨positive v,ub⟩
  have size : (Icc 1 3 : Finset ℕ).card=3 := by decide
  have up := card_le_card imageSub
  rw [card_image_of_injective _ inj,size] at up
  have ls : L⊆B := filter_subset _ _
  have low := card_le_card ls
  have eq := eq_of_subset_of_card_le ls (by omega)
  have bc : B.card=3 := by omega
  have eqI := eq_of_subset_of_card_le imageSub (by rw [size,card_image_of_injective _ inj,bc])
  exact ⟨bc,eqI,fun v vm => (mem_filter.mp (show v∈L from eq ▸ vm)).2,by change C⊆B.biUnion _; rwa [← eq]⟩

end Graffiti384b.CliquePivot33
#print axioms Graffiti384b.CliquePivot33.shared
#print axioms Graffiti384b.CliquePivot33.paired
#print axioms Graffiti384b.CliquePivot33.cover
#print axioms Graffiti384b.CliquePivot33.three_cubics

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph CliquePivot33
open private OneEar.deg2 from OneEarFinish384b
open private Repair.triangles_le_choose from Repair384b
open private TrianglePrune.triangle_iff TrianglePrune.reach_closed from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every neighbor of the deleted zero vertex receives one unit of credit
when that vertex is retained. No set smaller than half the positive core
can meet the remaining requirements in a counterexample. -/
theorem rooted_tight (n : Fintype.card V=33) (t : (types G).card=33) (bad : bound G<gamma G) (z : V) :
    let P := ({z} : Finset V)ᶜ
    let H := G.induce (P : Set V)
    Tight H (univ.filter (fun v : P => G.Adj v.val z)) := by
  classical
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  let R := univ.filter (fun v : P => G.Adj v.val z)
  let emb : P ↪ V := Function.Embedding.subtype _
  change Tight H R
  intro D good
  let K := D.map emb
  have zk : z∉K := by
    intro m
    obtain ⟨v,_,eq⟩ := mem_map.mp m
    exact mem_compl.mp v.property (mem_singleton.mpr eq)
  have counts (v : P) : nbr G v.val K=nbr H v D := by
    have eq : K.filter (G.Adj v.val)=(D.filter (H.Adj v)).map emb := by
      ext w; constructor
      · rintro hw
        obtain ⟨wk,adj⟩ := mem_filter.mp hw
        obtain ⟨u,um,rfl⟩ := mem_map.mp wk
        exact mem_map.mpr ⟨u,mem_filter.mpr ⟨um,adj⟩,rfl⟩
      · intro hw
        obtain ⟨u,um,rfl⟩ := mem_map.mp hw
        exact mem_filter.mpr ⟨mem_map.mpr ⟨u,(mem_filter.mp um).1,rfl⟩,(mem_filter.mp um).2⟩
    exact (congrArg card eq).trans (card_map ..)
  have dom : TwoDominates G (insert z K) := by
    intro v out
    have ne : v≠z := fun eq => out (eq ▸ mem_insert_self ..)
    let w : P := ⟨v,mem_compl.mpr (fun m => ne (mem_singleton.mp m))⟩
    have absent : w∉D := fun wm => out (mem_insert_of_mem (mem_map.mpr ⟨w,wm,rfl⟩))
    have h := good w absent
    change 2≤nbr H w D+(if w∈R then 1 else 0) at h
    rw [← counts w] at h
    have rel : w∈R ↔ G.Adj v z := by simp [R,w]
    change 2≤(K.filter (G.Adj v)).card+(if w∈R then 1 else 0) at h
    change 2≤((insert z K).filter (G.Adj v)).card
    by_cases adj : G.Adj v z
    · rw [filter_insert,if_pos adj,card_insert_of_not_mem (fun m => zk (mem_filter.mp m).1)]
      simpa only [if_pos (rel.mpr adj)] using h
    · rw [filter_insert,if_neg adj]
      simpa only [if_neg (fun m => adj (rel.mp m)),Nat.add_zero] using h
  have cap : gamma G≤(insert z K).card := Nat.sInf_le ⟨_,dom,rfl⟩
  rw [card_insert_of_not_mem zk,show K.card=D.card from card_map ..] at cap
  have size : Fintype.card P=32 := (Fintype.card_coe P).trans (by simp only [P,card_compl,card_singleton,n])
  unfold bound at bad; rw [n,t] at bad
  change Fintype.card P≤2*D.card
  omega

private theorem positive_clique {z : V} (zz : trianglesAt G z=0) {C : Finset V} (cl : G.IsNClique 5 C) :
    let P := ({z} : Finset V)ᶜ
    ∃ K,(G.induce (P : Set V)).IsNClique 5 K := by
  classical
  let P := ({z} : Finset V)ᶜ
  have zc : z∉C := by
    intro m
    have sz : (C.erase z).card=4 := by rw [card_erase_of_mem m,cl.2]
    obtain ⟨a,am,b,bm,ne⟩ := one_lt_card.mp (by omega : 1<(C.erase z).card)
    obtain ⟨az,ac⟩ := mem_erase.mp am
    obtain ⟨bz,bc⟩ := mem_erase.mp bm
    have pos := (TrianglePrune.triangle_iff G z).mpr ⟨a,b,cl.1 m ac az.symm,cl.1 m bc bz.symm,cl.1 ac bc ne⟩
    omega
  have keep (v : V) (vm : v∈C) : v∈P := mem_compl.mpr (fun m => zc ((mem_singleton.mp m) ▸ vm))
  let K := C.subtype (fun v => v∈P)
  have map : K.map (Function.Embedding.subtype _)=C := subtype_map_of_mem keep
  refine ⟨K,⟨fun u um v vm ne => cl.1 (mem_subtype.mp um) (mem_subtype.mp vm) (fun eq => ne (Subtype.ext eq)),?_⟩⟩
  exact (card_map ..).symm.trans ((congrArg card map).trans cl.2)

/-- Either the unique score-one vertex is a true unrooted ear, or the core
has three cubic vertices, all unrooted, with the displayed cover on every
five-clique. The whole surviving graph is the induced positive core. -/
theorem dichotomy (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    (fail : bound G<gamma G) (inj : Function.Injective (trianglesAt G))
    {z a : V} (zz : trianglesAt G z=0) (za : G.Adj z a) :
    let P := ({z} : Finset V)ᶜ
    let H := G.induce (P : Set V)
    let R := univ.filter (fun v : P => G.Adj v.val z)
    let B := univ.filter (fun v : P => H.degree v=3)
    (∃ e : P,trianglesAt H e=1 ∧ H.degree e=2 ∧ e∉R) ∨
    ((∀ v,3≤H.degree v) ∧ B.card=3 ∧ B.image (trianglesAt H)=Icc 1 3 ∧
      (∀ v∈B,v∉R) ∧ (∀ C,H.IsNClique 5 C → (∀ v∈B,v∉C ∧ nbr H v C≤2) ∧
        C⊆B.biUnion (fun v => C.filter (H.Adj v)))) := by
  classical
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  let R := univ.filter (fun v : P => G.Adj v.val z)
  let B := univ.filter (fun v : P => H.degree v=3)
  obtain ⟨_,_,_,pos,distinct,_⟩ := extremal_core G n t conn fail inj zz za
  change ∀ v,0<trianglesAt H v at pos
  change Function.Injective (trianglesAt H) at distinct
  have tight : Tight H R := rooted_tight G n t fail z
  have min2 (v : P) : 2≤H.degree v := by
    obtain ⟨u,w,vu,vw,uw⟩ := (TrianglePrune.triangle_iff H v).mp (pos v)
    exact OneEar.deg2 H uw.ne vu vw
  have one (v : P) (d : H.degree v=2) : trianglesAt H v=1 := by
    have up := Repair.triangles_le_choose H v
    rw [d,Nat.choose_self] at up; have := pos v; omega
  by_cases low : ∃ e : P,H.degree e=2 ∧ e∉R
  · obtain ⟨e,de,er⟩ := low
    exact Or.inl ⟨e,one e de,de,er⟩
  have minimum (v : P) : 2≤H.degree v ∧ (v∉R → 3≤H.degree v) :=
    ⟨min2 v,fun vr => by have no : H.degree v≠2 := fun d => low ⟨v,d,vr⟩; have := min2 v; omega⟩
  have five : ¬G.CliqueFree 5 := fun f => (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free G conn (by omega) t.ge f)) fail
  simp only [CliqueFree,not_forall,Classical.not_not] at five
  obtain ⟨C,cl⟩ := five
  obtain ⟨K,kc⟩ := positive_clique G zz cl
  have all (C : Finset P) (cl : H.IsNClique 5 C) := three_cubics H R minimum pos distinct tight cl
  obtain ⟨size,image,rr,_⟩ := all K kc
  have has : 1∈B.image (trianglesAt H) := by rw [show B.image (trianglesAt H)=Icc 1 3 from image]; decide
  obtain ⟨y,ym,ys⟩ := mem_image.mp has
  have yd : H.degree y=3 := (mem_filter.mp ym).2
  have min3 (v : P) : 3≤H.degree v := by
    have ne : H.degree v≠2 := fun d => by
      have eq := distinct ((one v d).trans ys.symm)
      subst v; omega
    have := min2 v; omega
  exact Or.inr ⟨min3,size,image,fun v vm => (rr v vm).2.1,fun C cl =>
    ⟨fun v vm => ⟨((all C cl).2.2.1 v vm).1,((all C cl).2.2.1 v vm).2.2⟩,(all C cl).2.2.2⟩⟩

/-- The zero-count vertex never meets the unique score-one vertex in an exact
33-vertex failure, even if the zero vertex originally has two neighbors. -/
theorem zero_one_separated (n : Fintype.card V=33) (t : (types G).card=33)
    (conn : G.Connected) (fail : bound G<gamma G) (inj : Function.Injective (trianglesAt G))
    {z : V} (zz : trianglesAt G z=0) : ∃ y,trianglesAt G y=1 ∧ ¬G.Adj z y ∧ (G.degree y=2 ∨ G.degree y=3) := by
  classical
  have neighbor : ∃ a,G.Adj z a := by
    apply Classical.byContradiction; intro none
    have every (v : V) : v∈({z} : Finset V) := TrianglePrune.reach_closed G {z} (by
      intro u um w uw
      obtain rfl := mem_singleton.mp um
      exact (none ⟨w,uw⟩).elim) (mem_singleton_self _) (conn z v)
    have eq := eq_univ_of_forall every
    have num := congrArg card eq
    rw [card_singleton,card_univ,n] at num
    omega
  obtain ⟨a,za⟩ := neighbor
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  let R := univ.filter (fun v : P => G.Adj v.val z)
  obtain ⟨_,_,sc,_,_,_⟩ := extremal_core G n t conn fail inj zz za
  have finish (y : P) (one : trianglesAt H y=1) (yr : y∉R) (d : H.degree y=2 ∨ H.degree y=3) :
      ∃ v,trianglesAt G v=1 ∧ ¬G.Adj z v ∧ (G.degree v=2 ∨ G.degree v=3) := by
    have yz : ¬G.Adj y.val z := fun edge => yr (mem_filter.mpr ⟨mem_univ _,edge⟩)
    have eq : (H.neighborFinset y).map (Function.Embedding.subtype _)=G.neighborFinset y.val := by
      ext v; constructor
      · intro vm
        obtain ⟨w,wm,rfl⟩ := mem_map.mp vm
        exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp wm)
      · intro vm
        have vy := (G.mem_neighborFinset _ _).mp vm
        have vp : v∈P := mem_compl.mpr (fun m => yz ((mem_singleton.mp m) ▸ vy))
        exact mem_map.mpr ⟨⟨v,vp⟩,(H.mem_neighborFinset _ _).mpr vy,rfl⟩
    have de := congrArg card eq
    rw [card_map,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at de
    exact ⟨y.val,(sc y).symm.trans one,fun h => yz h.symm,de ▸ d⟩
  rcases dichotomy G n t conn fail inj zz za with ⟨e,es,ed,er⟩|⟨_,_,image,roots,_⟩
  · exact finish e es er (Or.inl ed)
  · let B := univ.filter (fun v : P => H.degree v=3)
    have one : 1∈B.image (trianglesAt H) := by rw [show B.image (trianglesAt H)=Icc 1 3 from image]; decide
    obtain ⟨y,ym,score⟩ := mem_image.mp one
    exact finish y score (roots _ ym) (Or.inr (mem_filter.mp ym).2)

theorem exact_of_missing_one (conn : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=33)
    (miss : 1∉types G) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro fail
  obtain ⟨s,sz,hc,same,inj,_,⟨z,zero,_⟩,bad⟩ := OneEar.diversity33_failure G conn hn fail t
  let J := G.induce (s : Set V)
  obtain ⟨y,one,_,_⟩ := zero_one_separated J ((Fintype.card_coe s).trans sz) ((congrArg card same).trans t) hc bad inj zero
  exact miss (same ▸ mem_image.mpr ⟨y,mem_univ _,one⟩)

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.rooted_tight
#print axioms Graffiti384b.PositiveCore33.dichotomy
#print axioms Graffiti384b.PositiveCore33.zero_one_separated
#print axioms Graffiti384b.PositiveCore33.exact_of_missing_one
