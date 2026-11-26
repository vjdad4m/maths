import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
/-! AutoGraphForge normalized rows 371 and 808. -/
namespace Graffiti326
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel G.Adj

def HasMatching (G : SimpleGraph V) (k : ℕ) :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

local instance (G : SimpleGraph V) : DecidablePred (HasMatching G) := Classical.decPred _

private def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (Fintype.card V / 2+1)).filter (HasMatching G)

private theorem matchingSizes_nonempty (G : SimpleGraph V) :
    (feasibleMatchingSizes G).Nonempty := by
  use 0
  simp only [feasibleMatchingSizes, mem_filter, mem_range]
  refine ⟨by omega, ⟨⟨fun p => Fin.elim0 p.1, ?_⟩, ?_⟩⟩
  · intro p; exact Fin.elim0 p.1
  · intro i; exact Fin.elim0 i

def matchingNumber (G : SimpleGraph V) : ℕ :=
  (feasibleMatchingSizes G).max' (matchingSizes_nonempty G)

theorem matchingNumber_attained (G : SimpleGraph V) : HasMatching G (matchingNumber G) := by
  exact (Finset.mem_filter.1 (Finset.max'_mem (feasibleMatchingSizes G)
    (matchingSizes_nonempty G))).2

theorem matchingNumber_upper {G : SimpleGraph V} {k : ℕ} (hk : HasMatching G k) :
    k ≤ matchingNumber G := by
  obtain ⟨f,hf⟩ := hk
  have hk' : 2*k ≤ Fintype.card V := by
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective
  apply Finset.le_max'
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨f,hf⟩⟩

def support {k : ℕ} (f : Fin k × Bool ↪ V) : Finset V :=
  univ.map f

theorem mem_support {k : ℕ} (f : Fin k × Bool ↪ V) {v : V} :
    v ∈ support f ↔ ∃ i b, f (i,b) = v := by
  simp [support, Prod.exists]

theorem support_card {k : ℕ} (f : Fin k × Bool ↪ V) : (support f).card = 2*k := by
  simp [support, Nat.mul_comm]

theorem matching_extend_support {G : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) (ha : G.Adj x y) :
    ∃ f' : Fin (k+1) × Bool ↪ V, (∀ i, G.Adj (f' (i,false)) (f' (i,true))) ∧
      support f' ⊆ insert x (insert y (support f)) := by
  let F (i : Fin (k+1)) (b : Bool) :=
    Fin.lastCases (motive := fun _ => V) (if b then y else x) (fun j => f (j,b)) i
  have hX (i : Fin k) (b : Bool) : f (i,b) ∈ support f := (mem_support f).mpr ⟨i,b,rfl⟩
  have hfin : Function.Injective (fun p : Fin (k+1) × Bool => F p.1 p.2) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    change F i b = F j c at he
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl
    · simp only [F, Fin.lastCases_castSucc] at he
      obtain e := f.injective he
      cases e
      rfl
    · simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      cases c
      · change f (i,b) = x at he
        exact (hx (he ▸ hX i b)).elim
      · change f (i,b) = y at he
        exact (hy (he ▸ hX i b)).elim
    · simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      cases b
      · change x = f (j,c) at he
        exact (hx (he.symm ▸ hX j c)).elim
      · change y = f (j,c) at he
        exact (hy (he.symm ▸ hX j c)).elim
    · simp only [F, Fin.lastCases_last] at he
      cases b <;> cases c <;> simp_all [ha.ne,ha.ne.symm]
  let f' : Fin (k+1) × Bool ↪ V := ⟨fun p => F p.1 p.2,hfin⟩
  refine ⟨f', ?_, ?_⟩
  · intro i
    change G.Adj (F i false) (F i true)
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl
    · simpa [F] using hf i
    · simpa [F] using ha
  · intro z hz
    obtain ⟨i,b,rfl⟩ := (mem_support f').mp hz
    change F i b ∈ _
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl
    · simp only [F, Fin.lastCases_castSucc]
      exact mem_insert_of_mem (mem_insert_of_mem (hX i b))
    · cases b <;> simp [F]

theorem matching_extend {G : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) (ha : G.Adj x y) :
    HasMatching G (k+1) := by
  obtain ⟨f',hf',_⟩ := matching_extend_support hf hx hy ha
  exact ⟨f',hf'⟩

end
end Graffiti326

namespace AutoGraphForge371
open Finset SimpleGraph Function
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
section Forcing
variable {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj]

/-- The simultaneous step and fixed iteration count from the pinned GraphInvariants.lean. -/
def step (S : Finset U) : Finset U :=
  S ∪ univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, G.neighborFinset v \ S = {w})
def Total (S : Finset U) : Prop :=
  (step G)^[Fintype.card U] S = univ ∧ ∀ v ∈ S, ∃ w ∈ S, G.Adj v w
noncomputable def totalNumber := sInf {k | ∃ S : Finset U, S.card = k ∧ Total G S}


private def closure (S : Finset U) := (step G)^[Fintype.card U] S
private def Closed (S : Finset U) := step G S = S
private theorem below (S : Finset U) : S ⊆ step G S := subset_union_left

private theorem seed_le (S : Finset U) (n : ℕ) : S ⊆ (step G)^[n] S := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => rw [iterate_succ_apply']; exact ih.trans (below _ _)

private theorem closure_closed (S : Finset U) : Closed G (closure G S) := by
  have grow_or_eq (k : ℕ) : k ≤ ((step G)^[k] S).card ∨ Closed G ((step G)^[k] S) := by
    induction k with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ k ih =>
      rw [iterate_succ_apply']
      let R := (step G)^[k] S
      by_cases fix : Closed G R
      · exact Or.inr (by change Closed G (step G R); rw [show step G R = R from fix]; exact fix)
      · have large : R.card < (step G R).card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨below _ _,fun h => fix h.symm⟩)
        exact Or.inl (Nat.succ_le_of_lt (lt_of_le_of_lt (ih.resolve_right fix) large))
  rcases grow_or_eq (Fintype.card U) with big | done
  · change Fintype.card U ≤ (closure G S).card at big
    have all := (subset_iff_eq_of_card_le (by simpa using big :
        (univ : Finset U).card ≤ (closure G S).card)).mp (subset_univ _)
    rw [all]
    simp [Closed,step]
  · exact done

/-- A closed blue set admits a force whenever every other neighbor is blue. -/
private theorem force_into {R : Finset U} (cl : Closed G R) {u v : U}
    (hu : u ∈ R) (uv : G.Adj u v) (rest : ∀ w, G.Adj u w → w ≠ v → w ∈ R) : v ∈ R := by
  by_contra hv
  have eq : G.neighborFinset u \ R = {v} := by
    ext w
    simp only [mem_sdiff,mem_neighborFinset,mem_singleton]
    constructor
    · exact fun h => Classical.byContradiction (fun ne => h.2 (rest _ h.1 ne))
    · rintro rfl; exact ⟨uv,hv⟩
  have mem : v ∈ step G R := mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hv,u,hu,eq⟩)
  exact hv (cl ▸ mem)

private theorem closure_le {S R : Finset U} (sub : S ⊆ R) (cl : Closed G R) :
    closure G S ⊆ R := by
  have advance (T : Finset U) (ht : T ⊆ R) : step G T ⊆ R := by
    intro w hw
    rcases mem_union.mp hw with blue | neww
    · exact ht blue
    · obtain ⟨_,v,hv,eq⟩ := (mem_filter.mp neww).2
      have e := (mem_sdiff.mp (eq.symm ▸ mem_singleton_self w)).1
      apply force_into G cl (ht hv) ((G.mem_neighborFinset _ _).mp e)
      intro x ex ne
      apply ht
      by_contra miss
      have m := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ex,miss⟩
      rw [eq,mem_singleton] at m
      exact ne m
  have iter (k : ℕ) : (step G)^[k] S ⊆ R := by
    induction k with
    | zero => exact sub
    | succ k ih => rw [iterate_succ_apply']; exact advance _ ih
  exact iter _

end Forcing

def ClawFree {U : Type*} (G : SimpleGraph U) := ∀ v a b c : U,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- The endpoints of any maximal matching can be modified, at no extra cost,
to form an isolate-free zero-forcing set. -/
theorem swap_cover {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj]
    (cf : ClawFree G) (live : ∀ v, ∃ u, G.Adj v u) (B : Finset U) (mate : U → U)
    (paired : ∀ b ∈ B, mate b ∈ B ∧ G.Adj b (mate b) ∧ mate (mate b) = b)
    (ind : ∀ u ∉ B, ∀ v ∉ B, ¬G.Adj u v) : ∃ T, T.card ≤ B.card ∧ Total G T := by
  classical
  let M := closure G B
  have BM : B ⊆ M := seed_le G B _
  have clM : Closed G M := closure_closed G B
  let W := {v : U // v ∉ M}
  have out (w : W) : w.val ∉ B := fun h => w.2 (BM h)
  have wb (w : W) {b : U} (e : G.Adj w.val b) : b ∈ B :=
    Classical.byContradiction (fun hb => ind _ (out w) _ hb e)
  have pairwise (x y : W) : ¬G.Adj x.val y.val := ind _ (out x) _ (out y)
  -- Two white neighbors of the same endpoint are forced together in every
  -- closed superset of M: there cannot be a third independent white neighbor.
  have linked {b : U} (hb : b ∈ B) {x y : W} (bx : G.Adj b x.val) (by' : G.Adj b y.val)
      (R : Finset U) (MR : M ⊆ R) (clR : Closed G R) (hx : x.val ∈ R) : y.val ∈ R := by
    by_cases eq : x=y
    · exact eq ▸ hx
    apply force_into G clR (MR (BM hb)) by'
    intro z bz ne
    by_cases old : z ∈ M
    · exact MR old
    by_cases zx : z=x.val
    · exact zx ▸ hx
    let w : W := ⟨z,old⟩
    rcases cf b x.val y.val z bx by' bz (fun e => eq (Subtype.ext e)) (Ne.symm zx) (Ne.symm ne)
      with h|h|h
    · exact (pairwise x y h).elim
    · exact (pairwise x w h).elim
    · exact (pairwise y w h).elim
  -- Identify white vertices that belong to precisely the same closed supersets.
  let rel : Setoid W := {
    r := fun x y => ∀ (R : Finset U), M ⊆ R → Closed G R → (x.val ∈ R ↔ y.val ∈ R)
    iseqv := ⟨fun _ _ _ _ => Iff.rfl,fun h R m c => (h R m c).symm,
      fun h h' R m c => (h R m c).trans (h' R m c)⟩ }
  let Q := Quotient rel
  let tag : W → Q := Quotient.mk rel
  have same {b : U} (hb : b ∈ B) {x y : W} (bx : G.Adj b x.val) (by' : G.Adj b y.val) :
      tag x = tag y :=
    Quotient.sound (show rel.r x y from fun R m c =>
      ⟨linked hb bx by' R m c, linked hb by' bx R m c⟩)
  have choose_pair (q : Q) : ∃ b ∈ B, ∃ x : W,
      tag x=q ∧ G.Adj b x.val ∧ G.Adj (mate b) x.val := by
    let x : W := Quotient.out q
    have xq : tag x=q := Quotient.out_eq q
    obtain ⟨b,xb⟩ := live x.val
    have hb := wb x xb
    have alt : ∃ y : W, y.val ≠ x.val ∧ G.Adj b y.val := by
      by_contra fail
      apply x.2
      apply force_into G clM (BM hb) xb.symm
      intro y by' ne
      exact Classical.byContradiction (fun nh => fail ⟨⟨y,nh⟩,ne,by'⟩)
    obtain ⟨y,yx,by'⟩ := alt
    obtain ⟨mt,bt,_⟩ := paired _ hb
    rcases cf b x.val y.val (mate b) xb.symm by' bt (Ne.symm yx)
      (fun e => out x (e ▸ mt)) (fun e => out y (e ▸ mt)) with xy | xt | yt
    · exact (pairwise x y xy).elim
    · exact ⟨b,hb,x,xq,xb.symm,xt.symm⟩
    · exact ⟨b,hb,y,(same hb by' xb.symm).trans xq,by',yt.symm⟩
  choose keep hkeep white tagw keepw matew using choose_pair
  let drop (q : Q) := mate (keep q)
  have hd (q : Q) : drop q ∈ B := (paired _ (hkeep q)).1
  have owner {q : Q} {w : W} (e : G.Adj (drop q) w.val) : tag w=q :=
    (same (hd q) e (matew q)).trans (tagw q)
  have dinj : Function.Injective drop := by
    intro p q eq
    have edge := matew p
    change G.Adj (drop p) _ at edge
    rw [eq] at edge
    exact (tagw p).symm.trans (owner edge)
  letI : Fintype Q := Fintype.ofFinite Q
  let D := univ.image drop
  let X := univ.image (fun q => (white q).val)
  let T := (B \ D) ∪ X
  have dB : D ⊆ B := by
    intro v hv
    obtain ⟨q,_,rfl⟩ := mem_image.mp hv
    exact hd q
  have inD (q : Q) : drop q ∈ D := mem_image.mpr ⟨q,mem_univ _,rfl⟩
  have inX (q : Q) : (white q).val ∈ X := mem_image.mpr ⟨q,mem_univ _,rfl⟩
  have inT (q : Q) : (white q).val ∈ T := mem_union_right _ (inX q)
  have kept (q : Q) : keep q ∈ T := by
    apply mem_union_left
    refine mem_sdiff.mpr ⟨hkeep q,?_⟩
    intro h
    obtain ⟨p,_,de⟩ := mem_image.mp h
    have edge : G.Adj (drop p) (white q).val := de ▸ keepw q
    have pq := (owner edge).symm.trans (tagw q)
    have clash : drop q = keep q := pq ▸ de
    exact (paired _ (hkeep q)).2.1.ne clash.symm

  refine ⟨T,?_,?_,?_⟩
  · have dx : X.card ≤ D.card := by
      dsimp [X,D]
      rw [card_image_of_injective _ dinj]
      exact card_image_le
    have sum := card_sdiff_add_card_eq_card dB
    have bound := card_union_le (B \ D) X
    change (B \ D ∪ X).card ≤ B.card
    omega
  · let Z := closure G T
    have closedZ : Closed G Z := closure_closed G T
    have tz : T ⊆ Z := seed_le G T _
    have bz : B ⊆ Z := by
      intro b hb
      by_cases gone : b ∈ D
      · obtain ⟨q,_,rfl⟩ := mem_image.mp gone
        apply force_into G closedZ (tz (inT q)) (matew q).symm
        intro u wu diff
        have ub := wb (white q) wu
        apply tz
        apply mem_union_left
        refine mem_sdiff.mpr ⟨ub,?_⟩
        intro ud
        obtain ⟨p,_,eq⟩ := mem_image.mp ud
        have sees : G.Adj (drop p) (white q).val := eq ▸ wu.symm
        have pq := (owner sees).symm.trans (tagw q)
        exact diff (eq.symm.trans (congrArg drop pq))
      · exact tz (mem_union_left _ (mem_sdiff.mpr ⟨hb,gone⟩))
    have mz : M ⊆ Z := closure_le G bz closedZ
    change Z=univ
    apply eq_univ_of_forall
    intro v
    by_cases vm : v ∈ M
    · exact mz vm
    · let w : W := ⟨v,vm⟩
      have eq : rel.r (white (tag w)) w := Quotient.exact (tagw (tag w))
      exact (eq Z mz closedZ).mp (tz (inT (tag w)))
  · intro b h
    rcases mem_union.mp h with stayed | added
    · obtain ⟨hb,_⟩ := mem_sdiff.mp stayed
      obtain ⟨hm,e,inv⟩ := paired _ hb
      by_cases gone : mate b ∈ D
      · obtain ⟨q,_,eq⟩ := mem_image.mp gone
        have ke : keep q = b := ((paired _ (hkeep q)).2.2).symm.trans
          ((congrArg mate eq).trans inv)
        exact ⟨_,inT q,ke ▸ keepw q⟩
      · exact ⟨_,mem_union_left _ (mem_sdiff.mpr ⟨hm,gone⟩),e⟩
    · obtain ⟨q,_,rfl⟩ := mem_image.mp added
      exact ⟨_,kept q,(keepw q).symm⟩

open Graffiti326
section Catalogue
variable {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj]

def HasMaximalMatching (k : ℕ) : Prop :=
  ∃ f : Fin k × Bool ↪ U, (∀ i, G.Adj (f (i,false)) (f (i,true))) ∧
    ∀ u ∉ support f, ∀ v ∉ support f, ¬G.Adj u v
noncomputable def minMaximalMatching := sInf {k | HasMaximalMatching G k}

omit [DecidableEq U] [DecidableRel G.Adj] in
private theorem maximum_maximal : HasMaximalMatching G (matchingNumber G) := by
  obtain ⟨f,edges⟩ := matchingNumber_attained G
  refine ⟨f,edges,?_⟩
  intro u hu v hv edge
  have impossible := matchingNumber_upper (matching_extend edges hu hv edge)
  omega

theorem total_le_matching_endpoints (cf : ClawFree G) (live : ∀ v, ∃ u, G.Adj v u)
    {k : ℕ} (maximal : HasMaximalMatching G k) :
    ∃ T : Finset U, T.card ≤ 2*k ∧ Total G T := by
  classical
  obtain ⟨f,edges,ind⟩ := maximal
  let B := support f
  let flip (p : Fin k × Bool) := (p.1,!p.2)
  let mate (v : U) := if h : ∃ p, f p = v then f (flip h.choose) else v
  have mate_eq (p : Fin k × Bool) : mate (f p) = f (flip p) := by
    have ex : ∃ q, f q = f p := ⟨p,rfl⟩
    simp only [mate,dif_pos ex,f.injective ex.choose_spec]
  have paired (b : U) (hb : b ∈ B) : mate b ∈ B ∧ G.Adj b (mate b) ∧ mate (mate b)=b := by
    obtain ⟨i,t,rfl⟩ := (mem_support f).mp hb
    rw [mate_eq,mate_eq]
    refine ⟨(mem_support f).mpr ⟨i,!t,rfl⟩,?_,?_⟩
    · cases t
      · exact edges i
      · exact (edges i).symm
    · cases t <;> rfl
  obtain ⟨T,le,works⟩ := swap_cover G cf live B mate paired ind
  exact ⟨T,le.trans_eq (support_card f),works⟩

/-- GraphCalc returns a number exactly when the graph of order at least two
has no isolated vertices. -/
theorem total_exists_iff : (∃ S : Finset U, Total G S) ↔ ∀ v, ∃ w, G.Adj v w := by
  classical
  constructor
  · rintro ⟨S,full,total⟩ v
    by_contra fail
    have sub : S ⊆ univ.erase v := by
      intro x hx
      refine mem_erase.mpr ⟨?_,mem_univ _⟩
      rintro rfl
      obtain ⟨w,_,e⟩ := total x hx
      exact fail ⟨w,e⟩
    have fixed : Closed G (univ.erase v) := by
      apply Subset.antisymm _ (below _ _)
      intro x hx
      by_contra outside
      obtain ⟨b,_,eq⟩ := (mem_filter.mp ((mem_union.mp hx).resolve_left outside)).2.2
      have xeq : x=v := by simpa using outside
      have adj := (mem_sdiff.mp (eq.symm ▸ mem_singleton_self x)).1
      exact fail ⟨b,xeq ▸ ((G.mem_neighborFinset _ _).mp adj).symm⟩
    have inside := closure_le G sub fixed
    change closure G S = univ at full
    rw [full] at inside
    exact (mem_erase.mp (inside (mem_univ v))).1 rfl
  · intro live
    refine ⟨univ,?_,?_⟩
    · exact iterate_fixed (show step G univ = univ by simp [step]) _
    · intro v _
      obtain ⟨w,e⟩ := live v
      exact ⟨w,mem_univ _,e⟩

theorem row371_defined (cf : ClawFree G) (defined : ∃ S : Finset U, Total G S) :
    totalNumber G ≤ 2*minMaximalMatching G := by
  have maxi := maximum_maximal G
  have ex : {k | HasMaximalMatching G k}.Nonempty := ⟨_,maxi⟩
  obtain ⟨T,bound,works⟩ := total_le_matching_endpoints G cf ((total_exists_iff G).mp defined)
    (show HasMaximalMatching G (minMaximalMatching G) from Nat.sInf_mem ex)
  exact (Nat.sInf_le (s := {k | ∃ S : Finset U, S.card=k ∧ Total G S})
    ⟨T,rfl,works⟩).trans bound

theorem row808_defined (cf : ClawFree G) (defined : ∃ S : Finset U, Total G S) :
    totalNumber G ≤ 2*matchingNumber G :=
  (row371_defined G cf defined).trans (Nat.mul_le_mul_left 2
    (Nat.sInf_le (s := {k | HasMaximalMatching G k}) (maximum_maximal G)))

/-- Pinned Lean's natural-number convention for an infeasible minimum is zero. -/
theorem row371 (cf : ClawFree G) : totalNumber G ≤ 2*minMaximalMatching G := by
  classical
  by_cases h : ∃ S : Finset U, Total G S
  · exact row371_defined G cf h
  · have empty : {k | ∃ S : Finset U, S.card=k ∧ Total G S} = ∅ :=
      Set.eq_empty_iff_forall_not_mem.mpr (fun _ ⟨S,_,hs⟩ => h ⟨S,hs⟩)
    simp [totalNumber,empty]

theorem row808 (cf : ClawFree G) : totalNumber G ≤ 2*matchingNumber G :=
  (row371 G cf).trans (Nat.mul_le_mul_left 2
    (Nat.sInf_le (s := {k | HasMaximalMatching G k}) (maximum_maximal G)))

#print axioms total_le_matching_endpoints
#print axioms total_exists_iff
#print axioms row371_defined
#print axioms row808_defined
#print axioms row371
#print axioms row808
end Catalogue
end AutoGraphForge371

