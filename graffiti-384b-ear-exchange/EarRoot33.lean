import EarAttachment33

namespace Graffiti384b.EarRoot33
open Finset SimpleGraph CliquePivot33 EarFrame33 EarAttachment33 EarExchange33
open private EarExchange33.count_insert from Exchange33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Complete test for attaching a leaf to a core with domination number 16:
the tested set is an ordinary minimum set of the leaf-deleted graph. -/
theorem attachment_iff (n : Fintype.card V=33) (t : (types G).card=33) {z a : V}
    (leaf : G.neighborFinset z={a}) :
    let P := ({z} : Finset V)ᶜ
    let H := G.induce (P : Set V)
    ∀ r : P,r.val=a → gamma H=16 → (gamma G≤bound G ↔ ∃ D,Exchange H r D) := by
  classical
  let P := ({z} : Finset V)ᶜ
  let H := G.induce (P : Set V)
  change ∀ r : P,r.val=a → gamma H=16 → (gamma G≤bound G ↔ ∃ D,Exchange H r D)
  intro r ra core
  have half : 2*gamma H=Fintype.card P := by
    rw [core,Fintype.card_coe,show P.card=32 by simp [P,card_compl,n]]
  have adj (v : P) : G.Adj v.val z ↔ v=r := by
    rw [adj_comm,← G.mem_neighborFinset,leaf,mem_singleton]
    exact ⟨fun h => Subtype.ext (h.trans ra.symm),fun h => h ▸ ra⟩
  have roots : univ.filter (fun v : P => G.Adj v.val z)={r} := by ext v; simp [adj]
  rw [← exchange_iff H r half]
  constructor
  · intro solved tight
    have available : {k : ℕ | ∃ D,TwoDominates G D ∧ D.card=k}.Nonempty :=
      ⟨_,univ,by simp [TwoDominates],rfl⟩
    obtain ⟨D,dom,sz⟩ := Nat.sInf_mem available
    change D.card=gamma G at sz
    have zm : z∈D := by
      by_contra absent
      have two := dom z absent
      have sub : D.filter (G.Adj z)⊆G.neighborFinset z :=
        fun v vm => (G.mem_neighborFinset _ _).mpr (mem_filter.mp vm).2
      have cap := card_le_card sub
      rw [leaf,card_singleton] at cap
      change 2≤(D.filter (G.Adj z)).card at two
      omega
    let E := D.erase z
    let S : Finset P := E.subtype (fun v => v∈P)
    let emb : P ↪ V := Function.Embedding.subtype _
    have sub : E⊆P := fun v vm => mem_compl.mpr (fun h => (mem_erase.mp vm).1 (mem_singleton.mp h))
    have embed : S.map emb=E := subtype_map_of_mem sub
    have cardS : S.card=D.card-1 := by
      rw [← card_map (f:=emb),embed]; exact card_erase_of_mem zm
    have good : Relaxed H {r} S := by
      intro v out
      have ne : v.val≠z := fun h => mem_compl.mp v.property (mem_singleton.mpr h)
      have outside : v.val∉D := fun m => out (mem_subtype.mpr (mem_erase.mpr ⟨ne,m⟩))
      have cnt : nbr H v S=nbr G v.val E := by
        have eq : (S.filter (H.Adj v)).map emb=E.filter (G.Adj v.val) := by
          rw [← embed]
          ext w
          constructor
          · intro m
            obtain ⟨j,jm,rfl⟩ := mem_map.mp m
            exact mem_filter.mpr ⟨mem_map.mpr ⟨j,(mem_filter.mp jm).1,rfl⟩,(mem_filter.mp jm).2⟩
          · intro m
            obtain ⟨j,jm,rfl⟩ := mem_map.mp (mem_filter.mp m).1
            exact mem_map.mpr ⟨j,mem_filter.mpr ⟨jm,(mem_filter.mp m).2⟩,rfl⟩
        exact (card_map ..).symm.trans (congrArg card eq)
      have h := dom v.val outside
      have step := EarExchange33.count_insert G z v.val (S:=E) (not_mem_erase z D)
      rw [show insert z E=D from insert_erase zm] at step
      rw [step] at h
      simpa only [mem_singleton,cnt,adj] using h
    have low := tight S good
    have order : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
    change Fintype.card P≤2*S.card at low
    rw [order,cardS] at low
    unfold bound at solved
    rw [n,t] at solved
    omega
  · intro loose
    apply le_of_not_gt
    intro bad
    have tight := PositiveCore33.rooted_tight G n t bad z
    change Tight H (univ.filter (fun v : P => G.Adj v.val z)) at tight
    exact loose (roots ▸ tight)

end Graffiti384b.EarRoot33
#print axioms Graffiti384b.EarRoot33.attachment_iff
