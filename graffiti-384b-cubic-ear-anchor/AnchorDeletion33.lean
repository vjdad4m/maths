import EarOnClique33

namespace Graffiti384b.EarAnchor
open Finset SimpleGraph CliquePivot33 EarExchange33
open private EarExchange33.count_insert from Exchange33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

def outside (e a c : V) : Finset V := ({e,a,c} : Finset V)ᶜ
def Covers (W X : Finset V) : Prop := X⊆W ∧ ∀ v∈W,v∉X → 2≤nbr H v X
def Meets (c : V) (X : Finset V) : Prop := ∃ v∈X,H.Adj c v

omit [Fintype V] [DecidableEq V] in
private theorem one_iff (c : V) (X : Finset V) : Meets H c X ↔ 1≤nbr H c X := by
  change (∃ v∈X,H.Adj c v) ↔ 0<(X.filter (H.Adj c)).card
  rw [card_pos]
  exact ⟨fun ⟨v,m,h⟩ => ⟨v,mem_filter.mpr ⟨m,h⟩⟩,fun ⟨v,m⟩ => ⟨v,(mem_filter.mp m).1,(mem_filter.mp m).2⟩⟩

theorem outside_mem {e a c v : V} : v∈outside e a c ↔ v≠e ∧ v≠a ∧ v≠c := by
  simp [outside,not_or]

theorem lift {e a c : V} (ea : H.Adj e a) (ec : H.Adj e c)
    {X : Finset V} (cov : Covers H (outside e a c) X) (meet : Meets H c X) :
    Relaxed H {a} (insert e X) := by
  intro v out
  have absent : v∉X := fun m => out (mem_insert_of_mem m)
  have ne : v≠e := fun eq => out (eq ▸ mem_insert_self ..)
  have en : e∉X := fun m => (outside_mem.mp (cov.1 m)).1 rfl
  rw [EarExchange33.count_insert H e v en]
  by_cases va : v=a
  · subst v; simp [ea.symm]
  by_cases vc : v=c
  · subst v; have h := (one_iff H c X).mp meet
    simp only [if_pos ec.symm,mem_singleton,if_neg va,Nat.add_zero]; omega
  have h := cov.2 v (outside_mem.mpr ⟨ne,va,vc⟩) absent
  omega

/-- Exact reduction at either ear anchor. The only additional requirement
on a 2-dominating set of the 29-vertex induced graph is to meet the opposite
anchor's neighborhood. The root may have any degree. -/
theorem exchange_iff_guarded {e a c : V} (ear : H.neighborFinset e={a,c})
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (n : Fintype.card V=32) (g : gamma H=16) :
    (∃ D,Exchange H a D) ↔ ∃ X,Covers H (outside e a c) X ∧ Meets H c X ∧ X.card≤14 := by
  classical
  have half : 2*gamma H=Fintype.card V := by omega
  constructor
  · rintro ⟨D,dom,sz,am,one,safe⟩
    have em : e∈D := by
      apply Classical.byContradiction
      intro out
      have three := safe e out ea
      have inc : D.filter (H.Adj e)⊆H.neighborFinset e :=
        fun v vm => (H.mem_neighborFinset _ _).mpr (mem_filter.mp vm).2
      have upper := card_le_card inc
      rw [ear,card_pair ac.ne] at upper; change 3≤(D.filter (H.Adj e)).card at three; omega
    have cm : c∉D := fun m => by
      have two := PinnedColor34.two H ec.ne ea.symm ac em m
      omega
    let X := (D.erase a).erase e
    have ex : e∉X := not_mem_erase e _
    have ax : a∉X := fun h => not_mem_erase a D (erase_subset _ _ h)
    have cx : c∉X := fun m => cm (erase_subset _ _ (erase_subset _ _ m))
    have sub : X⊆outside e a c := by
      intro v vm
      exact outside_mem.mpr ⟨fun eq => ex (eq ▸ vm),fun eq => ax (eq ▸ vm),fun eq => cx (eq ▸ vm)⟩
    have ei : e∈D.erase a := mem_erase.mpr ⟨ea.ne,em⟩
    have split (v : V) : nbr H v D=nbr H v X+(if H.Adj v e then 1 else 0)+(if H.Adj v a then 1 else 0) := by
      have p := EarExchange33.count_insert H a v (S:=D.erase a) (not_mem_erase a D)
      have q := EarExchange33.count_insert H e v (S:=X) ex
      rw [insert_erase am] at p
      rw [show insert e X=D.erase a from insert_erase ei] at q
      omega
    refine ⟨X,⟨sub,?_⟩,?_,?_⟩
    · intro v vm no
      obtain ⟨ve,va,vc⟩ := outside_mem.mp vm
      have out : v∉D := fun m => no (mem_erase.mpr ⟨ve,mem_erase.mpr ⟨va,m⟩⟩)
      have noE : ¬H.Adj v e := by
        intro edge
        have h := (H.mem_neighborFinset _ _).mpr edge.symm
        rw [ear] at h; simp [va,vc] at h
      have eq := split v
      rw [if_neg noE,Nat.add_zero] at eq
      by_cases adj : H.Adj v a
      · have := safe v out adj; rw [if_pos adj] at eq; omega
      · have := dom v out; rw [if_neg adj] at eq; omega
    · apply (one_iff H c X).mpr
      have eq := split c
      rw [if_pos ec.symm,if_pos ac.symm] at eq
      have := safe c cm ac.symm; omega
    · change ((D.erase a).erase e).card≤14
      rw [card_erase_of_mem ei,card_erase_of_mem am]; omega
  · rintro ⟨X,cov,meet,sz⟩
    apply (EarExchange33.exchange_iff H a half).mp
    intro tight
    have le := tight _ (lift H ea ec cov meet)
    have up := card_insert_le e X
    omega

/-- The guard is automatic if one neighbor of the opposite anchor has at
most one residual neighbor outside that anchor's neighborhood. -/
theorem automatic_guard {c v : V} {W X : Finset V} (vm : v∈W) (cv : H.Adj c v)
    (small : nbr H v (W\H.neighborFinset c)≤1) (cov : Covers H W X) : Meets H c X := by
  apply Classical.byContradiction
  intro none
  have miss (w : V) (m : w∈X) : ¬H.Adj c w := fun adj => none ⟨w,m,adj⟩
  have out : v∉X := fun m => miss v m cv
  have subs : X⊆W\H.neighborFinset c := fun w m => mem_sdiff.mpr ⟨cov.1 m,fun h => miss w m ((H.mem_neighborFinset _ _).mp h)⟩
  have lower := cov.2 v vm out
  have upper := Repair.nbr_mono H v subs
  omega

omit [Fintype V] in
theorem gamma_induced_iff {W : Finset V} {k : ℕ} :
    gamma (H.induce (W : Set V))≤k ↔ ∃ X,Covers H W X ∧ X.card≤k := by
  classical
  let J := H.induce (W : Set V)
  let emb : W ↪ V := Function.Embedding.subtype _
  have counts (S : Finset W) (v : W) : nbr H v.val (S.map emb)=nbr J v S := by
    have eq : (S.filter (J.Adj v)).map emb=(S.map emb).filter (H.Adj v.val) := by
      ext w
      constructor
      · rintro m
        obtain ⟨z,zm,rfl⟩ := mem_map.mp m
        exact mem_filter.mpr ⟨mem_map.mpr ⟨z,(mem_filter.mp zm).1,rfl⟩,(mem_filter.mp zm).2⟩
      · intro m
        obtain ⟨z,zm,rfl⟩ := mem_map.mp (mem_filter.mp m).1
        exact mem_map.mpr ⟨z,mem_filter.mpr ⟨zm,(mem_filter.mp m).2⟩,rfl⟩
    exact ((card_map ..).symm.trans (congrArg card eq)).symm
  constructor
  · intro small
    have available : {s : ℕ | ∃ D,TwoDominates J D ∧ D.card=s}.Nonempty := ⟨_,univ,by simp [TwoDominates],rfl⟩
    obtain ⟨D,dom,sz⟩ := Nat.sInf_mem available
    change D.card=gamma J at sz
    refine ⟨D.map emb,⟨fun w m => by obtain ⟨v,_,rfl⟩ := mem_map.mp m; exact v.property,?_⟩,?_⟩
    · intro v vm out
      let x : W := ⟨v,vm⟩
      change 2≤nbr H x.val (D.map emb)
      rw [counts]; exact dom x (fun m => out (mem_map.mpr ⟨x,m,rfl⟩))
    · rw [card_map,sz]; exact small
  · rintro ⟨X,cov,sz⟩
    let D : Finset W := X.subtype (fun v => v∈W)
    have eq : D.map emb=X := subtype_map_of_mem cov.1
    have good : TwoDominates J D := by
      intro v out
      rw [← counts,eq]; exact cov.2 v.val v.property (fun m => out (mem_subtype.mpr m))
    have upper : gamma J≤D.card := Nat.sInf_le ⟨_,good,rfl⟩
    have card := congrArg Finset.card eq
    rw [card_map] at card
    exact upper.trans (card ▸ sz)

theorem exchange_iff_ordinary {e a c : V} (ear : H.neighborFinset e={a,c})
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (n : Fintype.card V=32) (g : gamma H=16)
    (guard : ∃ v,v∈outside e a c ∧ H.Adj c v ∧ nbr H v (outside e a c\H.neighborFinset c)≤1) :
    (∃ D,Exchange H a D) ↔ gamma (H.induce (outside e a c : Set V))≤14 := by
  rw [exchange_iff_guarded H ear ea ec ac n g,gamma_induced_iff]
  obtain ⟨v,vm,cv,small⟩ := guard
  exact ⟨fun ⟨X,cov,_,sz⟩ => ⟨X,cov,sz⟩,fun ⟨X,cov,sz⟩ => ⟨X,cov,automatic_guard H vm cv small cov,sz⟩⟩

end Graffiti384b.EarAnchor
#print axioms Graffiti384b.EarAnchor.exchange_iff_guarded
#print axioms Graffiti384b.EarAnchor.automatic_guard
#print axioms Graffiti384b.EarAnchor.gamma_induced_iff
#print axioms Graffiti384b.EarAnchor.exchange_iff_ordinary
