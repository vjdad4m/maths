import ChoicePatch
namespace Graffiti384b.FiveChoice
open Finset SimpleGraph Four29
variable {V : Type*} [DecidableEq V]

/-- Repeated common deletion. Quotas, and the number of deletions one anchor
may veto, can depend on the current size and on the individual anchor. -/
theorem shrink (A B X : Finset V) (L : V→Finset (Finset V))
    (need budget : ℕ→V→ℕ) (two : ∀a∈A,∀p∈L a,p.card=2) (enough : 5≤X.card)
    (start : ∀a∈A,need X.card a≤(kept (L a) (B∪X)).card)
    (room : ∀n,5<n → n≤X.card → (∑a∈A,budget n a)<n)
    (strict : ∀n,5<n → n≤X.card → ∀a∈A,∀s,need n a≤s →
      let r := budget n a+1; r*need (n-1) a+s+r.choose 2<r*(s+1)) :
    ∃K⊆X,K.card=5 ∧ ∀a∈A,need 5 a≤(kept (L a) (B∪K)).card := by
  classical
  have go (n : ℕ) : ∀Y⊆X,Y.card=n → 5≤n →
      (∀a∈A,need n a≤(kept (L a) (B∪Y)).card) →
      ∃K⊆Y,K.card=5 ∧ ∀a∈A,need 5 a≤(kept (L a) (B∪K)).card := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Y yx yn ge current
      by_cases eq : n=5
      · exact ⟨Y,Subset.rfl,yn.trans eq,fun a am => eq ▸ current a am⟩
      have nx : n≤X.card := yn ▸ card_le_card yx
      obtain ⟨v,vy,valid⟩ := choose_erase A B Y L (need (n-1)) (budget n) two
        (by rw [yn]; exact room n (by omega) nx) (fun a am => strict n (by omega) nx a am _ (current a am))
      have card := card_erase_of_mem vy
      rw [yn] at card
      obtain ⟨K,ky,ks,win⟩ := ih (n-1) (by omega) (Y.erase v) ((erase_subset ..).trans yx) card (by omega) valid
      exact ⟨K,ky.trans (erase_subset ..),ks,win⟩
  exact go X.card X Subset.rfl rfl enough start

/-- Quotas for thinning from six through nine contacts to five.
The third argument singles out the anchor required to retain thirteen triangles. -/
def minorQuota (n : ℕ) := match n with
  | 5 => 2 | 6 => 4 | 7 => 8 | 8 => 16 | 9 => 32 | _ => 0
def majorQuota (n : ℕ) := match n with
  | 5 => 13 | 6 => 20 | 7 => 28 | 8 => 37 | 9 => 47 | _ => 0

private theorem minor_step {n s : ℕ} (lo : 5<n) (hi : n≤9) (large : minorQuota n≤s) :
    2*minorQuota (n-1)+s+(2:ℕ).choose 2<2*(s+1) := by
  have cases' : n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
  rcases cases' with rfl|rfl|rfl|rfl <;> simp [minorQuota] at * <;> omega
private theorem major_step {n s : ℕ} (lo : 5<n) (hi : n≤9) (large : majorQuota n≤s) :
    (n-3)*majorQuota (n-1)+s+(n-3).choose 2<(n-3)*(s+1) := by
  have cases' : n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
  rcases cases' with rfl|rfl|rfl|rfl <;> simp [majorQuota,Nat.choose_succ_succ] at * <;> omega

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Any carrier of six to nine pool vertices can be thinned to five using
only its four scores. Other pool vertices impose no restrictions. -/
theorem dense_carrier (t : (types G).card=29) (h : (high G).card=27) (q : (nonleaves G).card=29)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (X : Finset V) (xp : X⊆pool G e f) (lo : 5≤X.card) (hi : X.card≤9) {a : V}
    (ar : a∈roots G e f) (large : majorQuota X.card≤score G e f X a)
    (small : ∀v∈roots G e f,v≠a → minorQuota X.card≤score G e f X v) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have D := data_of_failure G t h q bad de df ne
  let need := fun n v => if v=a then majorQuota n else minorQuota n
  let b := fun (n : ℕ) (v : V) => if v=a then n-4 else 1
  have room (n : ℕ) (n5 : 5<n) : (∑v∈roots G e f,b n v)<n := by
    have three := card_erase_of_mem ar
    rw [D.rootsSize] at three
    have rest : (∑v∈(roots G e f).erase a,b n v)=3 := by
      calc
        _ = ∑_v∈(roots G e f).erase a,1 := sum_congr rfl (fun v vm => if_neg (mem_erase.mp vm).1)
        _ = 3 := by simp [three]
    have all := sum_erase_add (roots G e f) (b n) ar
    rw [rest,show b n a=n-4 by simp [b]] at all
    omega
  obtain ⟨K,kx,ks,good⟩ := shrink (roots G e f) (base G e f) X (link G) need b
    (fun v _ => link_two G v) lo (fun v vm => by
      by_cases eq : v=a
      · subst v; simpa [need,score] using large
      · simpa [need,eq,score] using small v vm eq)
    (fun n n5 _ => room n n5) (fun n n5 nx v _ s ss => by
      by_cases eq : v=a
      · subst v
        simp only [need,b,if_pos rfl] at ss ⊢
        rw [show n-4+1=n-3 by omega]
        exact major_step n5 (nx.trans hi) ss
      · simp only [need,b,if_neg eq] at ss ⊢
        exact minor_step n5 (nx.trans hi) ss)
  have maj : 13≤score G e f K a := by simpa [need,majorQuota,score] using good a ar
  have win := five_chosen G t h q de df ne (kx.trans xp) ks (fun v vm => by
    by_cases eq : v=a
    · subst v; omega
    · simpa [need,minorQuota,eq,score] using good v vm) ar maj
  exact (not_lt_of_ge win) bad

/-- Direct application with all triangle contacts as the initial carrier. -/
theorem dense_contact_scores (t : (types G).card=29) (h : (high G).card=27) (q : (nonleaves G).card=29)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (lo : 5≤(triangleContacts G e f).card) (hi : (triangleContacts G e f).card≤9) {a : V}
    (ar : a∈roots G e f) (large : majorQuota (triangleContacts G e f).card≤trianglesAt G a)
    (small : ∀v∈roots G e f,v≠a → minorQuota (triangleContacts G e f).card≤trianglesAt G v) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  have D := data_of_failure G t h q bad de df ne
  exact (not_lt_of_ge (dense_carrier G t h q de df ne (triangleContacts G e f) (filter_subset ..) lo hi ar
    (by rw [all_contacts G D ar]; exact large) (fun v vm vn => by rw [all_contacts G D vm]; exact small v vm vn))) bad
end Graffiti384b.FiveChoice
#print axioms Graffiti384b.FiveChoice.shrink
#print axioms Graffiti384b.FiveChoice.dense_carrier
#print axioms Graffiti384b.FiveChoice.dense_contact_scores
