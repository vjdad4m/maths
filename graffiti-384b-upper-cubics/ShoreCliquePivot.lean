import Mathlib.Combinatorics.SimpleGraph.Clique
import Prune384b
import PinnedColor34_384b
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

