import PrimeChart180
import RootBonus180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 PortParity
open Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Both tests are evaluated inside the prime graph. The second arises
when a minimal failed pinned graph is obtained by adjoining an adjacent
true twin to its root. -/
def PrimeTests (G : SimpleGraph V) (r : V) : Prop :=
  (∀ p A,Indep G A → Pinned G r p A (A∩parity G r p)) ∧
  (∀ I,Indep G I → r∈I → OddRootTest G r I)

theorem universal_prime_tests (all : Assembly180.Universal.{u}) (G : SimpleGraph V)
    (gc : G.Connected) (high : 2<Fintype.card V) (r : V) (no : ∀ y,¬DomEdge G r y) : PrimeTests G r := by
  classical
  refine ⟨fun p A ai => universal_pins all G gc high r p A _ ai Subset.rfl,?_⟩
  intro I ii ir
  have nh (i : V) : ¬Universal G i := by
    intro hub
    have idB : Bags G G id := ⟨Function.surjective_id,fun _ => Iff.rfl⟩
    obtain ⟨y,ed⟩ := idB.hubEdge gc (by omega) hub r
    exact no y ed
  let h := twinChart G r
  have hc := h.bags.connected gc (by omega)
  have big : 2<Fintype.card (V⊕Unit) := by rw [Fintype.card_sum]; omega
  apply (h.odd_iff gc high nh I ir).mp
  exact universal_pins all _ hc big (.inr ()) true _ _ (h.ind_image ii) Subset.rfl

theorem minimal_prime_test (H : SimpleGraph V) (hc : H.Connected) (high : 2<Fintype.card V)
    (min : SmallerPinned H) (r : V) (p : Bool) (A : Finset V) (ai : Indep H A)
    (bad : ¬Pinned H r p A (A∩parity H r p))
    (tests : ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → ∀ a,(∀ j,¬DomEdge G a j) → PrimeTests G a) : False := by
  classical
  have no (y : V) (ed : DomEdge H r y) := bad (dominating_pins H hc high ed p A ai)
  have form := pin_minimal_module H hc high min r p A ai bad
  rcases prime_or_root_twin H r form with prime|⟨y,ry,hom,proper,_⟩
  · exact bad ((tests V H hc high prime r no).1 p A ai)
  obtain ⟨ed,rfl,ya⟩ := min_pair_odd H hc high min r y ry hom proper p A ai bad
  let M : Finset V := {r,y}
  let J := side H (reps M y)
  let f := collapse M y
  let s : ↥(reps M y)→V := Subtype.val
  have h := pairChart H r y ry hom ed
  have rm : r∈M := by simp [M]
  have ym : y∈M := by simp [M]
  have jc := quotient_connected H hc M hom y ym
  have ord := (quotient_order M y ym (by simp [M,ry]) proper).1
  have prime := h.bags.prime_after_root_fold r y ry (members_same M y r y rm ym) form
  have nh := pin_nohub h.bags jc ord high r true A ai bad
  have jn := three_of_nohub J jc ord nh
  have nop (i : ↥(reps M y)) (e : DomEdge J (f r) i) : False := by
    have lift : DomEdge J (f r) (f (s i)) := by
      have eq : f (s i)=i := h.sec i
      rw [eq]; exact e
    exact no (s i) (h.bags.domLift lift)
  have ra : r∉A := fun ar => ai r ar y ya ry ed
  let I := pull s A
  have ir : f r∈I := mem_pull.mpr (by simpa [f,s,collapse_val,rm] using ya)
  have lower := (tests _ J jc jn prime (f r) nop).2 I (h.ind_pull ai) ir
  have up := (h.odd_iff jc jn nh I ir).mpr lower
  have eq : I.image s=A := h.image_pull ra
  change Pinned H r true (I.image s) (I.image s∩parity H r true) at up
  exact bad (eq ▸ up)

/-- Exact ordinary #180 reduction to two internal inequalities on prime
connected graphs. A root incident to a dominating edge requires no test. -/
theorem universal_iff_prime_tests : Assembly180.Universal.{u} ↔
    ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W),G.Connected →
      2<Fintype.card W → Prime G → ∀ r,(∀ y,¬DomEdge G r y) → PrimeTests G r := by
  constructor
  · intro all W _ _ G gc high _ r no
    exact universal_prime_tests all G gc high r no
  · intro tests
    have prove (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) (gc : G.Connected)
        (hn : 1<Fintype.card W) : ∀ r p A,Indep G A → Pinned G r p A (A∩parity G r p) := by
      generalize eq : Fintype.card W=n at *
      induction n using Nat.strong_induction_on generalizing W with
      | h n ih =>
        intro r p A ai
        have ord : 1<Fintype.card W := by omega
        by_cases enough : 2<Fintype.card W
        · by_contra bad
          apply minimal_prime_test G gc enough _ r p A ai bad tests
          intro S small order con
          exact ih (Fintype.card ↥S) (by rw [Fintype.card_coe,←eq]; exact small) ↥S (side G S) con rfl
            (by simpa only [Fintype.card_coe] using order)
        · exact small_pinned G gc ord (by omega) r p A ai
    apply universal_iff_root_pairs.mpr
    intro W _ _ G gc high r _ _ p A ai
    exact prove W G gc (by omega) r p A ai

#print axioms universal_prime_tests
#print axioms minimal_prime_test
#print axioms universal_iff_prime_tests
end Minimal180.Substitution
