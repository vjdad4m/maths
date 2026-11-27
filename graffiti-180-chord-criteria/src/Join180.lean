import Cut180
import Exchange180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Converse180 Rooted180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def push {S : Finset V} (F : Finset ↥S) : Finset V :=
  F.map ⟨Subtype.val,Subtype.val_injective⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem in_push {S : Finset V} {F : Finset ↥S} (v : ↥S) : v.val ∈ push F ↔ v ∈ F := by
  change (⟨Subtype.val,Subtype.val_injective⟩ : ↥S ↪ V) v ∈ _ ↔ _
  exact mem_map' _
omit [Fintype V] [DecidableEq V] in
theorem push_sub {S : Finset V} (F : Finset ↥S) : push F ⊆ S := by
  rintro _ h
  obtain ⟨a,_,rfl⟩ := mem_map.mp h
  exact a.property
omit [Fintype V] [DecidableEq V] in
@[simp] theorem card_push {S : Finset V} (F : Finset ↥S) : (push F).card = F.card := card_map _
omit [Fintype V] in
theorem push_pull (S X : Finset V) : push (pull (fun v : ↥S => v.val) X) = X ∩ S := by
  ext v
  by_cases h : v ∈ S
  · simpa only [mem_inter,h,and_true] using (in_push (F:=pull _ X) ⟨v,h⟩).trans mem_pull
  · exact ⟨fun k => (h (push_sub _ k)).elim,fun k => (h (mem_inter.mp k).2).elim⟩

noncomputable def weight (x : V) (S : Finset V) : ℕ := if x ∈ S then 1 else 0
omit [Fintype V] in
theorem card_trim (S : Finset V) (x : V) : (S.erase x).card + weight x S = S.card := by
  by_cases h : x∈S
  · simpa only [weight,if_pos h] using card_erase_add_one h
  · simp [weight,h,erase_eq_of_not_mem h]

namespace Split
variable {c : V} {S T : Finset V} (s : Split G c S T)
include s
theorem tally (X : Finset V) :
    (pull (fun v : ↥S => v.val) X).card + (pull (fun v : ↥T => v.val) X).card =
      X.card + weight c X := by
  rw [← card_push,← card_push (pull (fun v : ↥T => v.val) X),push_pull,push_pull]
  have h := card_union_add_card_inter (X ∩ S) (X ∩ T)
  have un : X ∩ S ∪ X ∩ T = X := by rw [← inter_union_distrib_left,s.cover,inter_univ]
  have mi : (X ∩ S) ∩ (X ∩ T) = X ∩ {c} := by rw [← s.meet]; ext v; simp only [mem_inter]; tauto
  rw [un,mi] at h
  by_cases e : c∈X <;> simpa [weight,e,inter_singleton_of_mem,inter_singleton_of_not_mem] using h.symm

theorem trim_disj (A : Finset ↥S) (B : Finset ↥T) :
    Disjoint ((push A).erase c) ((push B).erase c) := disjoint_left.mpr fun _ h k =>
  (mem_erase.mp h).1 (s.common (push_sub _ (mem_of_mem_erase h)) (push_sub _ (mem_of_mem_erase k)))

end Split

private def Proper (H : SimpleGraph V) (A : Finset V) (f : V → Bool) : Prop :=
  ∀ ⦃v w⦄, v∈A → w∈A → H.Adj v w → f v ≠ f w

omit [Fintype V] in
private theorem normalize {H : SimpleGraph V} {A : Finset V} (hc : TwoColor H A) (x : V) :
    ∃ f, f x = false ∧ Proper H A f := by
  classical
  obtain ⟨B,C,dis,rfl,ib,ic⟩ := hc
  let f (v : V) := decide (v∈B)
  have good : Proper H (B ∪ C) f := by
    intro v w hv hw e eq
    by_cases a : v∈B
    · have b : w∈B := by by_contra h; simp [f,a,h] at eq
      exact ib _ a _ b e.ne e
    · have b : w∉B := by intro h; simp [f,a,h] at eq
      exact ic _ ((mem_union.mp hv).resolve_left a) _ ((mem_union.mp hw).resolve_left b) e.ne e
  cases h : f x
  · exact ⟨f,h,good⟩
  · exact ⟨fun v => !(f v),by simp [h],fun {_ _} hv hw e eq => good hv hw e (Bool.not_inj eq)⟩

omit [Fintype V] in
private theorem color_of_proper {H : SimpleGraph V} {A : Finset V} {f : V → Bool} (ok : Proper H A f) :
    TwoColor H A := by
  classical
  refine ⟨A.filter (fun v => f v=false),A.filter (fun v => f v=true),?_,?_,?_,?_⟩
  · exact disjoint_left.mpr (fun v hv hk => Bool.false_ne_true ((mem_filter.mp hv).2.symm.trans (mem_filter.mp hk).2))
  · ext v; cases h : f v <;> simp [h]
  all_goals
    intro v hv w hw _ e
    exact ok (mem_filter.mp hv).1 (mem_filter.mp hw).1 e ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)

private theorem bipWitness (H : SimpleGraph V) : ∃ A, TwoColor H A ∧ A.card = bipartiteNum H := by
  classical
  obtain ⟨A,hm,e⟩ := exists_mem_eq_sup (s:=univ.filter (TwoColor H)) (f:=card)
    ⟨∅,mem_filter.mpr ⟨mem_univ _,∅,∅,by simp,by simp,by simp [Indep],by simp [Indep]⟩⟩
  exact ⟨A,(mem_filter.mp hm).2,e.symm⟩

namespace Split
variable {c : V} {S T : Finset V} (s : Split G c S T)
include s
/-- Normalize the two colorings at the seam. Retain the seam exactly when
both sides selected it. At most one counted vertex is lost. -/
theorem bip_join : bipartiteNum (side G S)+bipartiteNum (side G T) ≤ bipartiteNum G+1 := by
  classical
  let l : ↥S := ⟨c,s.both.1⟩
  let t : ↥T := ⟨c,s.both.2⟩
  obtain ⟨A,ha,ae⟩ := bipWitness (side G S)
  obtain ⟨B,hb,be⟩ := bipWitness (side G T)
  obtain ⟨f,fc,fa⟩ := normalize ha l
  obtain ⟨g,gc,gb⟩ := normalize hb t
  let F (v : V) := if v∈S then f (s.proj v) else g (s.flip.proj v)
  have fl (v : ↥S) : F v.val=f v := by simp only [F,if_pos v.property,s.proj_in]
  have fr (v : ↥T) : F v.val=g v := by
    by_cases vs : v.val∈S
    · have eq : v=t := Subtype.ext (s.common vs v.property)
      subst v
      rw [show F t.val=f l from fl l,fc,gc]
    · simp only [F,if_neg vs,s.flip.proj_in]
  let X := univ.filter (fun v => (v∈S → v∈push A) ∧ (v∈T → v∈push B))
  have ok : Proper G X F := by
    intro v w hv hw e
    have hv' := (mem_filter.mp hv).2
    have hw' := (mem_filter.mp hw).2
    rcases s.edges e with h|h
    · rw [fl ⟨v,h.1⟩,fl ⟨w,h.2⟩]
      exact fa ((in_push ⟨v,h.1⟩).mp (hv'.1 h.1)) ((in_push ⟨w,h.2⟩).mp (hw'.1 h.2)) e
    · rw [fr ⟨v,h.1⟩,fr ⟨w,h.2⟩]
      exact gb ((in_push ⟨v,h.1⟩).mp (hv'.2 h.1)) ((in_push ⟨w,h.2⟩).mp (hw'.2 h.2)) e
  have bound : X.card ≤ bipartiteNum G := le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,color_of_proper ok⟩)
  let D := (push A).erase c ∪ (push B).erase c
  have dX : D = X.erase c := by
    ext v
    by_cases ne : v=c
    · simp [D,ne]
    · have exclusive : v∈S → v∈T → False := fun h k => ne (s.common h k)
      rcases s.either v with h|h
      · have nt : v ∉ T := exclusive h
        have nb : v ∉ push B := fun k => nt (push_sub _ k)
        simp [D,X,ne,h,nt,nb]
      · have ns : v∉S := fun k => exclusive k h
        have na : v ∉ push A := fun k => ns (push_sub _ k)
        simp [D,X,ne,h,ns,na]
  have dcard := card_union_of_disjoint (s.trim_disj A B)
  change D.card = _ at dcard
  rw [dX] at dcard
  have a := card_trim (push A) c
  have b := card_trim (push B) c
  have z := card_trim X c
  rw [card_push,ae] at a
  rw [card_push,be] at b
  have cx : c∈X ↔ c∈push A ∧ c∈push B := by simp [X,s.both.1,s.both.2]
  by_cases ca : c ∈ push A <;> by_cases cb : c ∈ push B <;>
    simp only [weight,cx,ca,cb,
      and_self,if_true,if_false,and_false,false_and] at a b z <;> omega
end Split
#print axioms Split.bip_join
end Assembly180
