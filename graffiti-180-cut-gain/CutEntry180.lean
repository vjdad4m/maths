import CutSupport180
import Weighted177Gain180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count the internal parent edges for a specified descending parent map,
using any depth function under which it descends one level. -/
theorem chosen_parent_count (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (r : V)
    (D : Finset V) (p : V→V) (depth : V→ℕ)
    (down : ∀ v≠r, depth v=depth (p v)+1) (take : ∀ v≠r, T.Adj v (p v)) :
    (T.edgeFinset∩D.sym2).card=((D.erase r).filter (fun v => p v∈D)).card := by
  classical
  let f (v : V) := s(v,p v)
  have inj {i j} (ir : i≠r) (jr : j≠r) (same : f i=f j) : i=j := by
    rcases Sym2.eq_iff.mp same with h|⟨h,k⟩
    · exact h.1
    · have a := (down i ir)
      have b := (down j jr)
      rw [k] at a
      rw [← h] at b
      omega
  have sub : (univ.erase r).image f⊆T.edgeFinset := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (take i (mem_erase.mp hi).1)
  have card := card_image_of_injOn (s:=univ.erase r) (f:=f)
    (fun i hi j hj equ => inj (mem_erase.mp hi).1 (mem_erase.mp hj).1 equ)
  have erase := card_erase_add_one (mem_univ r)
  rw [card_univ] at erase
  have all := eq_of_subset_of_card_le sub (by have := tr.card_edgeFinset; omega)
  let K := (D.erase r).filter (fun v => p v∈D)
  have form : T.edgeFinset∩D.sym2=K.image f := by
    ext e
    constructor
    · intro he
      obtain ⟨old,ind⟩ := mem_inter.mp he
      rw [← all] at old
      obtain ⟨v,hv,rfl⟩ := mem_image.mp old
      obtain ⟨vd,pd⟩ := mk_mem_sym2_iff.mp ind
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_erase.mpr ⟨(mem_erase.mp hv).1,vd⟩,pd⟩,rfl⟩
    · intro he
      obtain ⟨v,hv,rfl⟩ := mem_image.mp he
      obtain ⟨vr,pd⟩ := mem_filter.mp hv
      obtain ⟨ne,vd⟩ := mem_erase.mp vr
      exact mem_inter.mpr ⟨mem_edgeFinset.mpr (take v ne),mk_mem_sym2_iff.mpr ⟨vd,pd⟩⟩
  rw [form,card_image_of_injOn (s:=K) (f:=f) (fun i hi j hj eq =>
    inj (mem_erase.mp (mem_filter.mp hi).1).1 (mem_erase.mp (mem_filter.mp hj).1).1 eq)]

namespace TightCut
variable {J : SimpleGraph V} {S T : Finset V} {x y w : V} {r : ↥S} {odd : Bool} {A : Finset V}
variable (h : TightCut J S T x y w r odd A)
include h

/-- All possible shortest-path entries into the symmetric difference go
through one triangle tip. The root is outside that difference, and the
parity mark must strictly outnumber the independent mark. -/
theorem defect_one_entry (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    let D := (A∪P)\(A∩P)
    ¬weightedLeaves J U<weightedLeaves G U →
      r.val∉D ∧ A.card<P.card ∧ ∃ t∈({x,y}:Finset V), t∈D ∧
        ∀ i∈D, ∀ q, J.Adj i q → J.dist i r.val=J.dist q r.val+1 → q∉D → i=t := by
  classical
  intro G P U D ng
  obtain ⟨nw,xp,yp,miss,which⟩ := h.defect_one_support rank1 ng
  have neq : A≠P := fun s => miss s.le
  have wd : w∉D := fun d => nw (mem_sdiff.mp d).1
  obtain ⟨_,dx,dy⟩ := seam_layers h.connected h.split h.farTip h.rightSpoke h.absent r h.horizontal
  have nr {v : V} (e : J.dist v r.val=J.dist w r.val+1) : v≠r.val := by
    intro eq
    rw [eq,dist_self] at e
    omega
  obtain ⟨t,tp,td,tw,dt⟩ : ∃ t∈({x,y}:Finset V), t∈D ∧ J.Adj t w ∧ J.dist t r.val=J.dist w r.val+1 := by
    rcases which with k|k
    · exact ⟨y,by simp,mem_sdiff.mpr ⟨mem_union_right _ yp,fun z => k.2.1 (mem_inter.mp z).1⟩,h.rightSpoke.symm,dy⟩
    · exact ⟨x,by simp,mem_sdiff.mpr ⟨mem_union_right _ xp,fun z => k.2.1 (mem_inter.mp z).1⟩,h.leftSpoke,dx⟩
  have same {j : V} (e : G.Adj r.val j) : J.Adj r.val j := by
    rcases e with e|e
    · exact e
    rcases ((edge_adj ..).mp e).1 with k|k
    · exact (nr dx k.1.symm).elim
    · exact (nr dy k.1.symm).elim
  obtain ⟨l,m,rl,rm,lm⟩ := block_neighbors G (h.connected.mono le_sup_left) (by have := h.order; omega) h.block r.val
  have ai : Indep J A := fun i a j b diff e => h.independent i a j b diff (Or.inl e)
  have parent (p : V→V) (spec : ∀ v≠r.val, J.Adj v (p v) ∧ J.dist v r.val=J.dist (p v) r.val+1)
      (atTip : p t=w) :
      r.val∉D ∧ ∀ i∈D, i≠t → p i∈D := by
    obtain ⟨M,mj,tree,cross,take,star⟩ := predecessor_tree J h.connected r.val odd p spec
    have internal : r.val∉leaves M := fun leaf => lm (leaf_unique M leaf (star l (same rl)) (star m (same rm)))
    have op {i j : V} (e : M.Adj i j) : i∈P ↔ j∉P := by
      change i∈parity G r.val odd ↔ j∉parity G r.val odd
      rw [←h.layers_eq]
      exact cross e
    obtain ⟨_,_,edges⟩ := one_defect_rigid J M tree mj (by have := h.order; omega) r.val internal A P ai neq op rank1 h.tight
    change (M.edgeFinset∩D.sym2).card+1=D.card at edges
    rw [chosen_parent_count M tree r.val D p (fun v => J.dist v r.val) (fun v vr => (spec v vr).2) take] at edges
    let F := (D.erase r.val).filter (fun v => p v∈D)
    have ft : F⊆D.erase t := by
      intro i iv
      obtain ⟨di,pi⟩ := mem_filter.mp iv
      refine mem_erase.mpr ⟨?_,mem_of_mem_erase di⟩
      rintro rfl
      exact wd (atTip ▸ pi)
    have cnt := card_erase_add_one td
    have fe : D.erase t=F := (eq_of_subset_of_card_le ft (by change _≤((D.erase r.val).filter _).card; omega)).symm
    have source : r.val∉D := by
      intro rd
      have f : r.val∈F := fe ▸ mem_erase.mpr ⟨(nr dt).symm,rd⟩
      exact (mem_erase.mp (mem_filter.mp f).1).1 rfl
    exact ⟨source,fun i di it => (mem_filter.mp (show i∈F from fe ▸ mem_erase.mpr ⟨it,di⟩)).2⟩
  let basic (v : V) := if e : v=r.val then r.val else (Graffiti169.exists_predecessor J h.connected r.val v e).choose
  have std (v : V) (vr : v≠r.val) : J.Adj v (basic v) ∧ J.dist v r.val=J.dist (basic v) r.val+1 := by
    simpa [basic,vr] using (Graffiti169.exists_predecessor J h.connected r.val v vr).choose_spec
  let p (v : V) := if v=t then w else basic v
  have spec (v : V) (vr : v≠r.val) : J.Adj v (p v) ∧ J.dist v r.val=J.dist (p v) r.val+1 := by
    by_cases eq : v=t
    · subst v; simpa [p] using And.intro tw dt
    · simpa [p,eq] using std v vr
  have root := (parent p spec (by simp [p])).1
  have inc : A⊆U := by
    intro i a
    apply eligible_iff.mpr
    refine ⟨Or.inl a,?_⟩
    by_cases ir : i=r.val
    · subst i
      right
      refine ⟨a,?_⟩
      apply Classical.byContradiction
      intro np
      exact root (mem_sdiff.mpr ⟨mem_union_left _ a,fun c => np (mem_inter.mp c).2⟩)
    · exact Or.inl ir
  have mass := h.independent_obstruction ng A inc h.independent
  change 2*A.card<A.card+P.card at mass
  refine ⟨root,by omega,t,tp,td,?_⟩
  intro i id q iq d nq
  apply Classical.byContradiction
  intro it
  let b (v : V) := if v=i then q else p v
  have ok (v : V) (vr : v≠r.val) : J.Adj v (b v) ∧ J.dist v r.val=J.dist (b v) r.val+1 := by
    by_cases eq : v=i
    · subst v; simpa [b] using And.intro iq d
    · simpa [b,eq] using spec v vr
  have forced := (parent b ok (by simp [b,p,Ne.symm it])).2 i id it
  exact nq (by simpa [b] using forced)

#print axioms chosen_parent_count
#print axioms defect_one_entry
end TightCut
end Minimal180.CutGain
