import Converse180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Converse180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable abbrev side (G : SimpleGraph V) (S : Finset V) := G.induce (S : Set V)

structure Split (G : SimpleGraph V) (c : V) (S T : Finset V) : Prop where
  cover : S ∪ T = univ
  meet : S ∩ T = {c}
  edges : ∀ {u v}, G.Adj u v → (u ∈ S ∧ v ∈ S) ∨ (u ∈ T ∧ v ∈ T)
  smallL : S.card < Fintype.card V
  smallR : T.card < Fintype.card V

namespace Split
variable {c : V} {S T : Finset V} (s : Split G c S T)
include s
theorem flip : Split G c T S :=
  ⟨union_comm S T ▸ s.cover, inter_comm S T ▸ s.meet,fun e => (s.edges e).symm,s.smallR,s.smallL⟩
theorem both : c ∈ S ∧ c ∈ T := mem_inter.mp (s.meet ▸ mem_singleton_self c)
theorem common {v : V} (vs : v ∈ S) (vt : v ∈ T) : v = c :=
  mem_singleton.mp (s.meet ▸ mem_inter.mpr ⟨vs,vt⟩)
theorem either (v : V) : v ∈ S ∨ v ∈ T := mem_union.mp (s.cover ▸ mem_univ v)
theorem largeL : 1 < Fintype.card ↥S := by
  classical
  have e := card_union_add_card_inter S T
  rw [s.cover,s.meet,card_singleton,card_univ] at e
  have := s.smallR
  simpa using (show 1<S.card by omega)

noncomputable def proj (v : V) : ↥S := if h : v ∈ S then ⟨v,h⟩ else ⟨c,s.both.1⟩
@[simp] theorem proj_in (v : ↥S) : s.proj v.val = v := by simp [proj]
theorem proj_other {v : V} (hv : v ∈ T) : s.proj v = ⟨c,s.both.1⟩ := by
  by_cases h : v ∈ S
  · obtain rfl := s.common h hv
    simp [proj,h]
  · simp [proj,h]

theorem connectedL (hc : G.Connected) : (side G S).Connected := by
  classical
  let cS : ↥S := ⟨c,s.both.1⟩
  have hf : Function.LeftInverse s.proj (fun v : ↥S => v.val) := s.proj_in
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨cS,fun b => ?_⟩
  let a := cS
  obtain ⟨w⟩ := hc a.val b.val
  have e := walk_project G (fun v : ↥S => v.val) s.proj (fun {u v} uv => by
    rcases s.edges uv with h|h
    · right
      simpa [proj,h.1,h.2] using uv
    · left
      rw [s.proj_other h.1,s.proj_other h.2]) w
  rwa [hf a,hf b] at e

/-- Distance to a root on one side is its intrinsic distance there. On the
other side, the two intrinsic distances through the cut vertex add. -/
theorem distances (hc : G.Connected) (r : ↥S) :
    (∀ v : ↥S, G.dist v.val r.val = (side G S).dist v r) ∧
    ∀ v : ↥T, G.dist v.val r.val =
      (side G T).dist v ⟨c,s.both.2⟩ + (side G S).dist ⟨c,s.both.1⟩ r := by
  classical
  let l : ↥S := ⟨c,s.both.1⟩
  let t : ↥T := ⟨c,s.both.2⟩
  let off := (side G S).dist l r
  let d (v : V) := (side G S).dist (s.proj v) r + (side G T).dist (s.flip.proj v) t
  have dl (v : ↥S) : d v.val = (side G S).dist v r := by
    unfold d
    rw [s.proj_in v,s.flip.proj_other v.property]
    change _ + (side G T).dist t t = _
    rw [dist_self,Nat.add_zero]
  have dr (v : ↥T) : d v.val = (side G T).dist v t + off := by
    unfold d
    rw [s.proj_other v.property,s.flip.proj_in v]
    exact Nat.add_comm _ _
  have cl := s.connectedL hc
  have cr := s.flip.connectedL hc
  have lip {W : Type u} {H : SimpleGraph W} (con : H.Connected) (a b z : W)
      (ab : H.Adj a b) : H.dist a z ≤ H.dist b z+1 := by
    have h := con.dist_triangle (u:=a) (v:=b) (w:=z)
    rw [dist_eq_one_iff_adj.mpr ab] at h
    omega
  obtain ⟨_,de⟩ := layers G r.val d (by rw [dl,dist_self]) (fun {a b} ab => by
    rcases s.edges ab with h|h
    · rw [dl ⟨a,h.1⟩,dl ⟨b,h.2⟩]
      exact lip cl _ _ _ ab
    · rw [dr ⟨a,h.1⟩,dr ⟨b,h.2⟩]
      have := lip cr (⟨a,h.1⟩ : ↥T) ⟨b,h.2⟩ t ab
      omega) (fun v ne => by
    by_cases vs : v ∈ S
    · let a : ↥S := ⟨v,vs⟩
      obtain ⟨b,ab,e⟩ := Graffiti169.exists_predecessor _ cl r a (fun h => ne (congrArg Subtype.val h))
      exact ⟨b.val,ab,by rw [dl a,dl b,e]⟩
    · let a : ↥T := ⟨v,(s.either v).resolve_left vs⟩
      have ac : a ≠ t := fun h => vs ((show v=c from congrArg Subtype.val h).symm ▸ s.both.1)
      obtain ⟨b,ab,e⟩ := Graffiti169.exists_predecessor _ cr t a ac
      exact ⟨b.val,ab,by rw [dr a,dr b,e]; omega⟩)
  exact ⟨fun v => (de _).trans (dl v),fun v => (de _).trans (dr v)⟩

end Split

/-- A connected block has no cut vertex. Using preconnectedness after
deletion admits the single edge as a block. Order at least two is separate. -/
def NoCut (G : SimpleGraph V) : Prop :=
  ∀ c : V, (G.induce ({c}ᶜ : Set V)).Preconnected

theorem split_of_cut (h : ¬NoCut G) : ∃ c S T, Split G c S T := by
  classical
  unfold NoCut at h
  push_neg at h
  obtain ⟨c,bad⟩ := h
  let H := G.induce ({c}ᶜ : Set V)
  change ¬∀ a b, H.Reachable a b at bad
  push_neg at bad
  obtain ⟨a,b,ab⟩ := bad
  let p (v : V) : Prop := ∃ w : ({c}ᶜ : Set V), w.val = v ∧ H.Reachable a w
  let S := univ.filter (fun v => v=c ∨ p v)
  let T := univ.filter (fun v => v=c ∨ ¬p v)
  have pa : p a.val := ⟨a,rfl,.refl _⟩
  have pb : ¬p b.val := fun ⟨w,e,h⟩ => ab ((Subtype.ext e : w=b) ▸ h)
  have edge {v w : V} (e : G.Adj v w) (wc : w≠c) : p v → p w := by
    rintro ⟨u,rfl,hu⟩
    exact ⟨⟨w,wc⟩,rfl,hu.trans (show H.Adj u ⟨w,wc⟩ from e).reachable⟩
  refine ⟨c,S,T,?_,?_,?_,?_,?_⟩
  · ext v; by_cases pv : p v <;> simp [S,T,pv]
  · ext v; by_cases pv : p v <;> simp [S,T,pv]
  · intro v w e
    simp only [S,T,mem_filter,mem_univ,true_and]
    by_cases pv : p v
    · exact Or.inl ⟨Or.inr pv,or_iff_not_imp_left.mpr (fun h => edge e h pv)⟩
    · by_cases vc : v=c
      · by_cases pw : p w
        · exact Or.inl ⟨Or.inl vc,Or.inr pw⟩
        · exact Or.inr ⟨Or.inl vc,Or.inr pw⟩
      · exact Or.inr ⟨Or.inr pv,Or.inr (fun pw => pv (edge e.symm vc pw))⟩
  · rw [← card_univ]
    apply card_lt_card (ssubset_univ_iff.mpr ?_)
    intro eq
    have k : b.val ∈ S := eq ▸ mem_univ _
    simp [S,pb,show b.val ≠ c from b.property] at k
  · rw [← card_univ]
    apply card_lt_card (ssubset_univ_iff.mpr ?_)
    intro eq
    have k : a.val ∈ T := eq ▸ mem_univ _
    simp [T,pa,show a.val ≠ c from a.property] at k

#print axioms Split.distances
#print axioms split_of_cut
end Assembly180
