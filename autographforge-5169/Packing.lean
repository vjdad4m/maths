import Patch

namespace Packing2560
open Finset SimpleGraph TriangleMatching1078 BullCover1125

variable {V : Type*} {G : SimpleGraph V}

/-- Vertex-disjoint induced copies of the bull. Edges between different copies
are allowed. -/
def HasPacking (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : Fin k → (bull ↪g G), ∀ i j, i ≠ j → ∀ u v, f i u ≠ f j v

noncomputable def bullPacking [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact ((range (Fintype.card V + 1)).filter (HasPacking G)).sup id

theorem packing_le [Fintype V] {I : Type*} [Fintype I] (f : I → (bull ↪g G))
    (sep : ∀ i j, i ≠ j → ∀ u v, f i u ≠ f j v) : Fintype.card I ≤ bullPacking G := by
  classical
  have size := Fintype.card_le_of_injective (fun i => f i 0) (fun i j eq =>
    Classical.byContradiction (fun ne => sep i j ne 0 0 eq))
  let e := (Fintype.equivFin I).symm
  have good : HasPacking G (Fintype.card I) :=
    ⟨fun i => f (e i), fun i j ne => sep _ _ (fun eq => ne (e.injective eq))⟩
  exact le_sup (f:=id) (b:=Fintype.card I) (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le size),good⟩)

/-- A partition of the vertices outside a dominating edge set by one
responsible edge each. Endpoints of different edges may initially coincide. -/
structure Patches (G : SimpleGraph V) (I : Type*) where
  left : I → V
  right : I → V
  outside : I → Finset V
  attached : ∀ i, Attached G (left i) (right i) (outside i)
  complete : ∀ v, ∃ i, v=left i ∨ v=right i ∨ v∈outside i
  unique : ∀ {i j v}, v∈outside i → v∈outside j → i=j
  separate : ∀ {i j v}, v∈outside i → v ≠ left j ∧ v ≠ right j
  independent : ∀ {i j x y}, x∈outside i → y∈outside j → ¬ G.Adj x y

theorem partition [Fintype V] (iso : IsolateFree G) {D : Finset G.edgeSet}
    (dom : Dominates G.lineGraph D) : Nonempty (Patches G ↥D) := by
  classical
  let S := univ.filter (fun v : V => ∃ e ∈ D, v ∈ e.val)
  have incident {v} : v ∈ S ↔ ∃ e ∈ D, v ∈ e.val := by simp [S]
  have hit {v w} (vw : G.Adj v w) : v ∈ S ∨ w ∈ S := by
    obtain ⟨e,he,z,ze,zw⟩ := (dominates_iff G D).mp dom ⟨s(v,w),vw⟩
    rcases Sym2.mem_iff.mp zw with rfl|rfl
    · exact Or.inl (incident.mpr ⟨_,he,ze⟩)
    · exact Or.inr (incident.mpr ⟨_,he,ze⟩)
  let l (e : ↥D) := e.val.val.out.1
  let r (e : ↥D) := e.val.val.out.2
  have repr (e : ↥D) : s(l e,r e) = e.val.val := e.val.val.out_eq
  have get (v : {x // x ∉ S}) : ∃ e : ↥D, G.Adj (l e) v.val ∨ G.Adj (r e) v.val := by
    obtain ⟨w,vw⟩ := iso v.val
    obtain ⟨f,hf,wf⟩ := incident.mp ((hit vw).resolve_left v.property)
    let e : ↥D := ⟨f,hf⟩
    change w ∈ e.val.val at wf
    rw [← repr e] at wf
    exact ⟨e,(Sym2.mem_iff.mp wf).elim (fun eq => Or.inl (eq ▸ vw.symm))
      (fun eq => Or.inr (eq ▸ vw.symm))⟩
  choose owner joins using get
  let X (e : ↥D) := univ.filter fun x : V => ∃ h : x ∉ S, owner ⟨x,h⟩ = e
  have owned {e x} : x ∈ X e ↔ ∃ h : x ∉ S, owner ⟨x,h⟩ = e := by simp [X]
  have away {i j : ↥D} {v} (hv : v ∈ X i) : v ≠ l j ∧ v ≠ r j := by
    obtain ⟨out,_⟩ := owned.mp hv
    constructor
    · rintro rfl
      exact out (incident.mpr ⟨j,j.property,Sym2.out_fst_mem _⟩)
    · rintro rfl
      exact out (incident.mpr ⟨j,j.property,Sym2.out_snd_mem _⟩)
  have ind {i j : ↥D} {x y} (hx : x ∈ X i) (hy : y ∈ X j) : ¬ G.Adj x y :=
    fun edge => (hit edge).elim (owned.mp hx).choose (owned.mp hy).choose
  refine ⟨⟨l,r,X,?_,?_,?_,away,ind⟩⟩
  · intro e
    refine ⟨show s(l e,r e) ∈ G.edgeSet from repr e ▸ e.val.property,
      fun _ hx => away hx,fun _ hx _ hy => ind hx hy,?_⟩
    intro x hx
    obtain ⟨out,eq⟩ := owned.mp hx
    exact eq ▸ joins ⟨x,out⟩
  · intro v
    by_cases h : v ∈ S
    · obtain ⟨f,hf,vf⟩ := incident.mp h
      let e : ↥D := ⟨f,hf⟩
      change v ∈ e.val.val at vf
      rw [← repr e] at vf
      exact ⟨e,(Sym2.mem_iff.mp vf).imp_right Or.inl⟩
    · exact ⟨owner ⟨v,h⟩,Or.inr (Or.inr (owned.mpr ⟨h,rfl⟩))⟩
  · intro i j v hi hj
    obtain ⟨_,ei⟩ := owned.mp hi
    obtain ⟨_,ej⟩ := owned.mp hj
    exact ei.symm.trans ej

/-- Two distinct patches with three assigned vertices cannot share an endpoint:
it would have three independent neighbors formed from their disjoint fibers. -/
theorem hubs_separate {I : Type*} (p : Patches G I) (cl : Free G claw) {i j : I} (ne : i ≠ j)
    (pi : Profile G (p.left i) (p.right i) (p.outside i))
    (pj : Profile G (p.left j) (p.right j) (p.outside j)) {v}
    (hi : v=p.left i ∨ v=p.right i) (hj : v=p.left j ∨ v=p.right j) : False := by
  obtain ⟨r,hr,s,hs,rs,vr,vs⟩ := profile_neighbors pi hi
  obtain ⟨t,ht,_,_,_,vt,_⟩ := profile_neighbors pj hj
  have rt : r ≠ t := fun eq => ne (p.unique (eq ▸ hr) ht)
  have st : s ≠ t := fun eq => ne (p.unique (eq ▸ hs) ht)
  exact (claw_neighbors cl vr vs vt rs rt st).elim (p.independent hr hs)
    (fun q => q.elim (p.independent hr ht) (p.independent hs ht))

theorem patch_estimate [Fintype V] {I : Type*} [Fintype I] (p : Patches G I) (cl : Free G claw) :
    ∃ P : Finset G.edgeSet, Covers G P ∧
      P.card ≤ 2 * Fintype.card I + min (Fintype.card I) (bullPacking G) := by
  classical
  let H := univ.filter fun i : I => 2 < (p.outside i).card
  have profile (e : ↥H) := (heavy_profile cl (p.attached e.val) (mem_filter.mp e.property).2).some
  choose copy location using fun e : ↥H => profile_copy (profile e) (p.attached e.val)
  have packed : H.card ≤ bullPacking G := by
    rw [← Fintype.card_coe H]
    apply packing_le copy
    intro i j ne u v eq
    have ij : i.val ≠ j.val := fun h => ne (Subtype.ext h)
    have li := location i u
    have lj := location j v
    rw [← eq] at lj
    rcases li with hi|hi|hi <;> rcases lj with hj|hj|hj
    · exact hubs_separate p cl ij (profile i) (profile j) (Or.inl hi) (Or.inl hj)
    · exact hubs_separate p cl ij (profile i) (profile j) (Or.inl hi) (Or.inr hj)
    · exact (p.separate hj).1 hi
    · exact hubs_separate p cl ij (profile i) (profile j) (Or.inr hi) (Or.inl hj)
    · exact hubs_separate p cl ij (profile i) (profile j) (Or.inr hi) (Or.inr hj)
    · exact (p.separate hj).2 hi
    · exact (p.separate hi).1 hj
    · exact (p.separate hi).2 hj
    · exact ij (p.unique hi hj)
  choose piece cost covers using fun i => patch_cover cl (p.attached i)
  refine ⟨univ.biUnion piece,?_,?_⟩
  · intro v
    obtain ⟨i,loc⟩ := p.complete v
    obtain ⟨f,hf,mem⟩ := covers i v loc
    exact ⟨f,mem_biUnion.mpr ⟨i,mem_univ _,hf⟩,mem⟩
  · calc
      _ ≤ ∑ i, (piece i).card := card_biUnion_le
      _ ≤ ∑ i, (2 + (if 2 < (p.outside i).card then 1 else 0)) := sum_le_sum fun i _ => cost i
      _ = 2 * Fintype.card I + H.card := by simp [H,sum_add_distrib,Nat.mul_comm,Finset.card_filter]
      _ ≤ _ := Nat.add_le_add_left (le_min (card_le_univ _) packed) _

theorem refined [Fintype V] (iso : IsolateFree G) (cl : Free G claw) :
    edgeCoverNumber G ≤ 2 * lineDomination G + min (lineDomination G) (bullPacking G) := by
  classical
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={k | ∃ D : Finset G.edgeSet,
    D.card=k ∧ Dominates G.lineGraph D}) ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination G at sz
  obtain ⟨p⟩ := partition iso dom
  obtain ⟨P,cover,cost⟩ := patch_estimate p cl
  rw [Fintype.card_coe,sz] at cost
  exact (Nat.sInf_le (s:={k | ∃ P : Finset G.edgeSet,P.card=k ∧ Covers G P})
    ⟨P,rfl,cover⟩).trans cost

end Packing2560
