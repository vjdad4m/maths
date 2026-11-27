import JoinLeaves180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Graffiti318 Converse180 Rooted180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
theorem eligible_iff {A P : Finset V} {v x : V} :
    v∈eligible A P x ↔ (v∈A ∨ v∈P) ∧ (v≠x ∨ (x∈A ∧ x∈P)) := by
  by_cases h : x∈A ∧ x∈P <;> simp [eligible,h]
  tauto

omit [Fintype V] in
private theorem loss {X : Finset V} (c : ↥X) (D : Finset ↥X) (Z : Finset V)
    (all : ∀ v∈D, v=c ∧ c.val∈Z) : D.card ≤ weight c.val Z := by
  classical
  by_cases h : c.val∈Z
  · have le : D ⊆ {c} := fun v hv => mem_singleton.mpr (all v hv).1
    simpa [weight,h] using card_le_card le
  · have nil : D=∅ := eq_empty_iff_forall_not_mem.mpr (fun v hv => h (all v hv).2)
    simp [nil,weight,h]

namespace Split
variable {c : V} {S T : Finset V} (s : Split G c S T)
include s
/-- The rooted inequality is closed under a one-vertex sum. Only membership
of the seam is counted twice. -/
theorem join_local (hc : G.Connected) (r : ↥S) (P : Finset V)
    (left : localBound (side G S) r (pull (fun v : ↥S => v.val) P))
    (right : localBound (side G T) ⟨c,s.both.2⟩ (pull (fun v : ↥T => v.val) P)) :
    localBound G r.val P := by
  classical
  intro A ai
  let t : ↥T := ⟨c,s.both.2⟩
  let l : ↥S := ⟨c,s.both.1⟩
  let U := eligible A P r.val
  let L (F : Finset V) := pull (fun v : ↥S => v.val) F
  let R (F : Finset V) := pull (fun v : ↥T => v.val) F
  let E := eligible (L A) (L P) r
  let F := eligible (R A) (R P) t
  have ind (X : Finset V) : Indep (side G X) (pull (fun v : ↥X => v.val) A) :=
    fun a ha b hb ne e => ai _ (mem_pull.mp ha) _ (mem_pull.mp hb) (fun h => ne (Subtype.ext h)) e
  have hl := left (L A) (ind S)
  have hr := right (R A) (ind T)
  change 1+(L A).card+(L P).card ≤ weightedLeaves (side G S) E+_ at hl
  change 1+(R A).card+(R P).card ≤ weightedLeaves (side G T) F+_ at hr
  have offL (v : ↥S) (hv : v∈E) : v.val∈U := by
    rw [eligible_iff] at hv ⊢
    exact ⟨hv.1.imp mem_pull.mp mem_pull.mp,hv.2.imp (fun h eq => h (Subtype.ext eq))
      (fun h => ⟨mem_pull.mp h.1,mem_pull.mp h.2⟩)⟩
  have dl := restrict_leaves (side G S) E (L (U.erase c))
  have dr := restrict_leaves (side G T) F (R (U.erase c))
  have ll := loss l (E \ L (U.erase c)) (A ∪ P) (fun v hv => by
    obtain ⟨ve,no⟩ := mem_sdiff.mp hv
    have inU := offL v ve
    have eq : v.val=c := Classical.byContradiction (fun ne => no (mem_pull.mpr (mem_erase.mpr ⟨ne,inU⟩)))
    refine ⟨Subtype.ext eq,?_⟩
    change c∈A∪P
    rw [← eq]
    exact mem_union.mpr (eligible_iff.mp inU).1)
  have lr := loss t (F \ R (U.erase c)) (A ∩ P) (fun v hv => by
    obtain ⟨ve,no⟩ := mem_sdiff.mp hv
    have info := eligible_iff.mp ve
    have eq : v.val=c := by
      apply Classical.byContradiction
      intro ne
      have vr : v.val≠r.val := fun h => ne (s.common (h.symm ▸ r.property) v.property)
      apply no
      apply mem_pull.mpr
      apply mem_erase.mpr
      exact ⟨ne,eligible_iff.mpr ⟨info.1.imp mem_pull.mp mem_pull.mp,Or.inl vr⟩⟩
    have vt : v=t := Subtype.ext eq
    obtain ⟨a,p⟩ := info.2.resolve_left (not_not.mpr vt)
    exact ⟨vt,mem_inter.mpr ⟨mem_pull.mp a,mem_pull.mp p⟩⟩)
  have leaves := s.leaf_join hc U
  change weightedLeaves (side G S) (L (U.erase c))+weightedLeaves (side G T) (R (U.erase c)) ≤ _ at leaves
  have bip := s.bip_join
  have ac := s.tally A
  have pc := s.tally P
  change (L A).card+(R A).card=_ at ac
  change (L P).card+(R P).card=_ at pc
  have count : weight l.val (A ∪ P)+weight t.val (A ∩ P)=weight c A+weight c P := by
    by_cases a : c∈A <;> by_cases p : c∈P <;> simp [l,t,weight,a,p]
  change 1+A.card+P.card ≤ weightedLeaves G U+bipartiteNum G
  omega

theorem parity_join (hc : G.Connected) (r : ↥S) (odd : Bool)
    (hl : ∀ (a : ↥S) p, localBound (side G S) a (parity (side G S) a p))
    (hr : ∀ (a : ↥T) p, localBound (side G T) a (parity (side G T) a p)) :
    localBound G r.val (parity G r.val odd) := by
  classical
  let t : ↥T := ⟨c,s.both.2⟩
  let off := (side G S).dist ⟨c,s.both.1⟩ r
  let p := if off%2=0 then odd else !odd
  have ds := s.distances hc r
  apply s.join_local hc r
  · have eq : pull (fun v : ↥S => v.val) (parity G r.val odd) = parity (side G S) r odd := by
      ext v; simp only [mem_pull,mem_parity,ds.1 v]
    rw [eq]; exact hl _ _
  · have eq : pull (fun v : ↥T => v.val) (parity G r.val odd) = parity (side G T) t p := by
      ext v
      simp only [mem_pull,mem_parity,ds.2 v]
      change ((side G T).dist v t+off)%2=odd.toNat ↔ (side G T).dist v t%2=p.toNat
      cases odd <;> by_cases h : off%2=0 <;> simp [p,h] <;> omega
    rw [eq]; exact hr _ _
end Split

def OnBlocks : Prop := ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  G.Connected → 1 < Fintype.card V → NoCut G → ∀ r odd, localBound G r (parity G r odd)
def Universal : Prop := ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  G.Connected → 1 < Fintype.card V → 1+independence G+maxEven G ≤ maxLeaves G+bipartiteNum G

theorem rooted_of_blocks (blocks : OnBlocks.{u}) (hc : G.Connected) (hn : 1<Fintype.card V) :
    ∀ r odd, localBound G r (parity G r odd) := by
  classical
  generalize eq : Fintype.card V = n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases ok : NoCut G
    · exact blocks V G hc (eq ▸ hn) ok
    obtain ⟨c,S,T,s⟩ := split_of_cut ok
    have next {X Y} (q : Split G c X Y) : ∀ (a : ↥X) p, localBound (side G X) a (parity (side G X) a p) := by
      exact ih (Fintype.card ↥X) (by rw [Fintype.card_coe,← eq]; exact q.smallL)
        (q.connectedL hc) rfl q.largeL
    intro r odd
    rcases s.either r with h|h
    · exact s.parity_join hc ⟨r,h⟩ odd (next s) (next s.flip)
    · exact s.flip.parity_join hc ⟨r,h⟩ odd (next s.flip) (next s)

theorem universal_iff_blocks : Universal.{u} ↔ OnBlocks.{u} := by
  classical
  constructor
  · intro all V _ _ H con hn _ r odd
    by_contra fail
    obtain ⟨W,f,d,J,jc,jn,_,bad⟩ := of_failed_local H con hn r odd fail
    letI := f
    letI := d
    exact (Nat.not_lt_of_ge (all W J jc jn)) bad
  · intro blocks V _ _ G con hn
    haveI : Nonempty V := con.nonempty
    obtain ⟨r,_,re⟩ := exists_mem_eq_sup (s:=univ) (f:=evenCount G) univ_nonempty
    obtain ⟨A,ha,ae⟩ := exists_mem_eq_sup (s:=univ.filter (Indep G)) (f:=card)
      ⟨∅,mem_filter.mpr ⟨mem_univ _,by simp [Indep]⟩⟩
    have bd := rooted_of_blocks blocks con hn r false A (mem_filter.mp ha).2
    have le : weightedLeaves G (eligible A (parity G r false) r) ≤ maxLeaves G := by
      rw [← weighted_all]
      exact (restrict_leaves G _ univ).trans (by simp)
    change maxEven G=evenCount G r at re
    change independence G=A.card at ae
    rw [re,ae,even_equiv]
    omega

#print axioms Split.join_local
#print axioms rooted_of_blocks
#print axioms universal_iff_blocks
end Assembly180
