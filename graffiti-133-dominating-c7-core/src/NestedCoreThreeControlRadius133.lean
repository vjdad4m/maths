import NestedCoreLongGateRadius133
import NestedCorePrivateWeightedGeometry133
import C7MultiWeightedGlobal133

namespace Graffiti133NestedThreeControls
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133NestedLongGates Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 7000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

def CloseProfile (i : Fin 7) (p : Fin 14) : Prop :=
  ∃ j : Fin 7,j∈profileContacts p ∧ (j=i ∨ Cyclic i j)

instance (i : Fin 7) (p : Fin 14) : Decidable (CloseProfile i p) := by unfold CloseProfile; infer_instance

def ThreeCover (p q r : Fin 14) (i : Fin 7) : Prop :=
  (∀ j : Fin 7,farSites i j →
    (i∈profileContacts p ∧ j∈profileContacts p) ∨
    (i∈profileContacts q ∧ j∈profileContacts q) ∨
    (i∈profileContacts r ∧ j∈profileContacts r)) ∧
  CloseProfile i p ∧ CloseProfile i q ∧ CloseProfile i r

instance (p q r : Fin 14) (i : Fin 7) : Decidable (ThreeCover p q r i) := by unfold ThreeCover; infer_instance

theorem compatible_three_have_center (p : Fin 14) : ∀ q r : Fin 14,
    p≠q → p≠r → q≠r → profileOK p q → profileOK p r → profileOK q r →
    ∃ i : Fin 7,ThreeCover p q r i := by
  fin_cases p <;> decide

private theorem two_steps (hc : G.Connected) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c≤2 := by
  have h : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at h
  exact h

theorem radius_three_of_three_control_core
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (D : Finset V) (cy : ∀ i,H.c i∈D)
    (ddom : ∀ x : V,x∈D ∨ ∃ y∈D,G.Adj x y)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (u v w : V) (ud : u∈D) (vd : v∈D) (wd : w∈D)
    (uo : Outside H.c u) (vo : Outside H.c v) (wo : Outside H.c w)
    (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (uh : (contactSet H u).Nonempty) (vh : (contactSet H v).Nonempty) (wh : (contactSet H w).Nonempty)
    (shape : ∀ x∈D,(∃ i,H.c i=x) ∨ x=u ∨ x=v ∨ x=w) :
    radius G≤3 := by
  let J := G.induce (D : Set V)
  let B := restrictedHole H D cy
  have cl {x : V} (xd : x∈D) (xo : Outside H.c x) (xh : (contactSet H x).Nonempty) :
      ∃ p,Matches B ⟨x,xd⟩ p := by
    apply classify_profile B (restricted_c4 h4 D) d7
    · exact fun i e=>xo i (congrArg Subtype.val e)
    · obtain ⟨i,im⟩ := xh
      exact ⟨i,(mem_contactSet H x i).mp im⟩
  obtain ⟨p,pu⟩ := cl ud uo uh
  obtain ⟨q,qv⟩ := cl vd vo vh
  obtain ⟨r,rw⟩ := cl wd wo wh
  have pp : Matches H u p := pu
  have qq : Matches H v q := qv
  have rr : Matches H w r := rw
  have prof {x y : V} {p q : Fin 14} (ne : x≠y) (px : Matches H x p) (qy : Matches H y q) : p≠q := by
    intro eq
    subst q
    have cap := disjoint_contact_pairs H h4 ne
    have a : contactSet H x=profileContacts p := by
      ext i
      exact (mem_contactSet H _ _).trans (px i)
    have b : contactSet H y=profileContacts p := by
      ext i
      exact (mem_contactSet H _ _).trans (qy i)
    rw [a,b,Finset.inter_self] at cap
    have := profile_at_least_two p
    omega
  have pq := prof uv pp qq
  have pr := prof uw pp rr
  have qr := prof vw qq rr
  have compatible {x y : V} {px qy : Fin 14} (xm : x∈D) (ym : y∈D)
      (xo : Outside H.c x) (yo : Outside H.c y) (ne : x≠y) (neq : px≠qy)
      (a : Matches B ⟨x,xm⟩ px) (b : Matches B ⟨y,ym⟩ qy) : profileOK px qy :=
    (classify_pair B (restricted_c4 h4 D) d7
      (fun i e=>xo i (congrArg Subtype.val e)) (fun i e=>yo i (congrArg Subtype.val e))
      (fun e=>ne (congrArg Subtype.val e)) neq a b).1
  obtain ⟨i,far,iu,iv,iw⟩ := compatible_three_have_center p q r pq pr qr
    (compatible ud vd uo vo uv pq pu qv)
    (compatible ud wd uo wo uw pr pu rw)
    (compatible vd wd vo wo vw qr qv rw)
  have ctl {x : V} {p : Fin 14} (xp : Matches H x p) (ip : CloseProfile i p) :
      G.dist (H.c i) x≤2 := by
    obtain ⟨j,jp,eq|ed⟩ := ip
    · subst j
      rw [dist_eq_one_iff_adj.mpr ((xp _).mpr jp).symm]
      decide
    · exact two_steps hc ((H.adj _ _).mpr ed) ((xp _).mpr jp).symm
  apply radius_three_from_core_cover hc D ddom (H.c i)
  intro x xm
  rcases shape x xm with ⟨j,rfl⟩|rfl|rfl|rfl
  · by_cases eq : i=j
    · rw [←eq,dist_self]
      decide
    by_cases near : Cyclic i j
    · rw [dist_eq_one_iff_adj.mpr ((H.adj i j).mpr near)]
      decide
    by_cases mid : ∃ k,Cyclic i k ∧ Cyclic j k
    · obtain ⟨k,ik,jk⟩ := mid
      exact two_steps hc ((H.adj i k).mpr ik) ((H.adj j k).mpr jk).symm
    · rcases far j ⟨eq,near,mid⟩ with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
      · exact two_steps hc ((pp i).mpr a).symm ((pp j).mpr b)
      · exact two_steps hc ((qq i).mpr a).symm ((qq j).mpr b)
      · exact two_steps hc ((rr i).mpr a).symm ((rr j).mpr b)
  · exact ctl pp iu
  · exact ctl qq iv
  · exact ctl rr iw

#print axioms compatible_three_have_center
#print axioms radius_three_of_three_control_core
end Graffiti133NestedThreeControls
