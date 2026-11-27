import DeletionClass180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- Replacing a single vertex of a nontrivial connected bipartite graph
with a nonempty clique leaves the maximum induced bipartite order equal
to the original order, independently of the clique size. -/
theorem Bags.oneCliqueOrder (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (bi : TwoColor G univ) (c : B) (cl : ∀ x y,f x=c → f y=c → x≠y → H.Adj x y)
    (single : ∀ x y,f x=f y → f x≠c → x=y) : bipartiteNum H=Fintype.card B := by
  classical
  obtain ⟨Z,col,opt⟩ := optB H
  let X := Z.filter (fun v => f v=c)
  let T := Z.filter (fun v => f v≠c)
  have inj : Set.InjOn f T := fun x hx y _ eq => single x y eq (mem_filter.mp hx).2
  have c_out : c∉T.image f := by
    rintro mem
    obtain ⟨v,vt,eq⟩ := mem_image.mp mem
    exact (mem_filter.mp vt).2 eq
  have split : X∪T=Z := by ext x; simp [X,T]; tauto
  have dis : Disjoint X T := disjoint_left.mpr
    (fun x hx ht => (mem_filter.mp ht).2 (mem_filter.mp hx).2)
  have count := congrArg card split
  rw [card_union_of_disjoint dis,opt] at count
  obtain ⟨C,D,dd,cd,ci,di⟩ := col
  have small {S : Finset V} (si : Indep H S) : (S∩X).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    exact si x (mem_inter.mp hx).1 y (mem_inter.mp hy).1 ne
      (cl x y (mem_filter.mp (mem_inter.mp hx).2).2 (mem_filter.mp (mem_inter.mp hy).2).2 ne)
  have cover : X⊆(C∩X)∪(D∩X) := by
    intro x hx
    rcases mem_union.mp (cd.symm ▸ (mem_filter.mp hx).1) with a|b
    · exact mem_union_left _ (mem_inter.mpr ⟨a,hx⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨b,hx⟩)
  have x2 := (card_le_card cover).trans (card_union_le ..)
  have := small ci
  have := small di
  have bound : X.card≤2 := by omega
  have upper : bipartiteNum H≤Fintype.card B := by
    by_cases dup : 1<X.card
    · obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp dup
      obtain ⟨j,cj⟩ := exists_adj G gc hn c
      obtain ⟨clr,good⟩ := (color_function H Z).mp ⟨C,D,dd,cd,ci,di⟩
      have xm := mem_filter.mp hx
      have ym := mem_filter.mp hy
      have xy := good x xm.1 y ym.1 (cl x y xm.2 ym.2 ne)
      have jout : j∉T.image f := by
        rintro jm
        obtain ⟨v,vt,fv⟩ := mem_image.mp jm
        have vz := (mem_filter.mp vt).1
        have xv := good x xm.1 v vz (h.edgeUp (by rw [xm.2,fv]; exact cj))
        have yv := good y ym.1 v vz (h.edgeUp (by rw [ym.2,fv]; exact cj))
        cases a : clr x <;> cases b : clr y <;> cases d : clr v <;> simp [a,b,d] at *
      have sz := card_le_univ (insert j (insert c (T.image f)))
      rw [card_insert_of_not_mem (by simp [cj.ne.symm,jout]),card_insert_of_not_mem c_out,card_image_of_injOn inj] at sz
      omega
    · have sz := card_le_univ (insert c (T.image f))
      rw [card_insert_of_not_mem c_out,card_image_of_injOn inj] at sz
      omega
  let s (i : B) := (h.onto i).choose
  have sec : Function.LeftInverse f s := fun i => (h.onto i).choose_spec
  have lower := h.colorExtra s sec univ bi ∅ (by simp [Indep]) (by simp) (by simp) (by simp)
  exact le_antisymm upper (by simpa using lower)

/-- The bipartization deficit is precisely the surplus order over the
base. The ordinary conjecture and both-parity rooted bounds still hold. -/
theorem Bags.oneCliqueDeficit (h : Bags H G f) (gc : G.Connected) (hn : 1<Fintype.card B)
    (bi : TwoColor G univ) (c : B) (cl : ∀ x y,f x=c → f y=c → x≠y → H.Adj x y)
    (single : ∀ x y,f x=f y → f x≠c → x=y) :
    Fintype.card V-bipartiteNum H=Fintype.card V-Fintype.card B ∧
    (∀ r p,localBound H r (parity H r p)) ∧
    1+independence H+Graffiti318.maxEven H≤maxLeaves H+bipartiteNum H :=
  ⟨by rw [h.oneCliqueOrder gc hn bi c cl single],h.bipartiteRooted gc hn bi,
    bipartite_substitution_ordinary h gc hn bi⟩

#print axioms Bags.oneCliqueOrder
#print axioms Bags.oneCliqueDeficit
end Minimal180.Substitution
