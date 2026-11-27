import LeafBound
import SmallChunk0
import SmallChunk1
import SmallChunk2
import SmallChunk3
import SmallChunk4
import SmallChunk5
import SmallChunk6
import SmallChunk7
import SmallChunk8

namespace CazenaveRank
set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 10000 in
set_option maxHeartbeats 15000000 in
theorem certSmall (n p : ℕ) (hn3 : 3≤n) (hn90 : n≤90) (hp : p≤n/2)
    (hn3p : n=3 → p=0) : intClaim n p := by

  by_cases h46 : n ≤ 46
  · by_cases h24 : n ≤ 24
    · by_cases h13 : n ≤ 13
      · by_cases h8 : n ≤ 8
        · by_cases h5 : n ≤ 5
          · by_cases h4 : n ≤ 4
            · by_cases h3 : n ≤ 3
              · have he : n = 3 := by omega
                have hh := hn3p he
                subst n; subst p; exact case3
              · have he : n = 4 := by omega
                subst n; exact case4 ⟨p, by omega⟩
            · have he : n = 5 := by omega
              subst n; exact case5 ⟨p, by omega⟩
          · by_cases h7 : n ≤ 7
            · by_cases h6 : n ≤ 6
              · have he : n = 6 := by omega
                subst n; exact case6 ⟨p, by omega⟩
              · have he : n = 7 := by omega
                subst n; exact case7 ⟨p, by omega⟩
            · have he : n = 8 := by omega
              subst n; exact case8 ⟨p, by omega⟩
        · by_cases h11 : n ≤ 11
          · by_cases h10 : n ≤ 10
            · by_cases h9 : n ≤ 9
              · have he : n = 9 := by omega
                subst n; exact case9 ⟨p, by omega⟩
              · have he : n = 10 := by omega
                subst n; exact case10 ⟨p, by omega⟩
            · have he : n = 11 := by omega
              subst n; exact case11 ⟨p, by omega⟩
          · by_cases h12 : n ≤ 12
            · have he : n = 12 := by omega
              subst n; exact case12 ⟨p, by omega⟩
            · have he : n = 13 := by omega
              subst n; exact case13 ⟨p, by omega⟩
      · by_cases h19 : n ≤ 19
        · by_cases h16 : n ≤ 16
          · by_cases h15 : n ≤ 15
            · by_cases h14 : n ≤ 14
              · have he : n = 14 := by omega
                subst n; exact case14 ⟨p, by omega⟩
              · have he : n = 15 := by omega
                subst n; exact case15 ⟨p, by omega⟩
            · have he : n = 16 := by omega
              subst n; exact case16 ⟨p, by omega⟩
          · by_cases h18 : n ≤ 18
            · by_cases h17 : n ≤ 17
              · have he : n = 17 := by omega
                subst n; exact case17 ⟨p, by omega⟩
              · have he : n = 18 := by omega
                subst n; exact case18 ⟨p, by omega⟩
            · have he : n = 19 := by omega
              subst n; exact case19 ⟨p, by omega⟩
        · by_cases h22 : n ≤ 22
          · by_cases h21 : n ≤ 21
            · by_cases h20 : n ≤ 20
              · have he : n = 20 := by omega
                subst n; exact case20 ⟨p, by omega⟩
              · have he : n = 21 := by omega
                subst n; exact case21 ⟨p, by omega⟩
            · have he : n = 22 := by omega
              subst n; exact case22 ⟨p, by omega⟩
          · by_cases h23 : n ≤ 23
            · have he : n = 23 := by omega
              subst n; exact case23 ⟨p, by omega⟩
            · have he : n = 24 := by omega
              subst n; exact case24 ⟨p, by omega⟩
    · by_cases h35 : n ≤ 35
      · by_cases h30 : n ≤ 30
        · by_cases h27 : n ≤ 27
          · by_cases h26 : n ≤ 26
            · by_cases h25 : n ≤ 25
              · have he : n = 25 := by omega
                subst n; exact case25 ⟨p, by omega⟩
              · have he : n = 26 := by omega
                subst n; exact case26 ⟨p, by omega⟩
            · have he : n = 27 := by omega
              subst n; exact case27 ⟨p, by omega⟩
          · by_cases h29 : n ≤ 29
            · by_cases h28 : n ≤ 28
              · have he : n = 28 := by omega
                subst n; exact case28 ⟨p, by omega⟩
              · have he : n = 29 := by omega
                subst n; exact case29 ⟨p, by omega⟩
            · have he : n = 30 := by omega
              subst n; exact case30 ⟨p, by omega⟩
        · by_cases h33 : n ≤ 33
          · by_cases h32 : n ≤ 32
            · by_cases h31 : n ≤ 31
              · have he : n = 31 := by omega
                subst n; exact case31 ⟨p, by omega⟩
              · have he : n = 32 := by omega
                subst n; exact case32 ⟨p, by omega⟩
            · have he : n = 33 := by omega
              subst n; exact case33 ⟨p, by omega⟩
          · by_cases h34 : n ≤ 34
            · have he : n = 34 := by omega
              subst n; exact case34 ⟨p, by omega⟩
            · have he : n = 35 := by omega
              subst n; exact case35 ⟨p, by omega⟩
      · by_cases h41 : n ≤ 41
        · by_cases h38 : n ≤ 38
          · by_cases h37 : n ≤ 37
            · by_cases h36 : n ≤ 36
              · have he : n = 36 := by omega
                subst n; exact case36 ⟨p, by omega⟩
              · have he : n = 37 := by omega
                subst n; exact case37 ⟨p, by omega⟩
            · have he : n = 38 := by omega
              subst n; exact case38 ⟨p, by omega⟩
          · by_cases h40 : n ≤ 40
            · by_cases h39 : n ≤ 39
              · have he : n = 39 := by omega
                subst n; exact case39 ⟨p, by omega⟩
              · have he : n = 40 := by omega
                subst n; exact case40 ⟨p, by omega⟩
            · have he : n = 41 := by omega
              subst n; exact case41 ⟨p, by omega⟩
        · by_cases h44 : n ≤ 44
          · by_cases h43 : n ≤ 43
            · by_cases h42 : n ≤ 42
              · have he : n = 42 := by omega
                subst n; exact case42 ⟨p, by omega⟩
              · have he : n = 43 := by omega
                subst n; exact case43 ⟨p, by omega⟩
            · have he : n = 44 := by omega
              subst n; exact case44 ⟨p, by omega⟩
          · by_cases h45 : n ≤ 45
            · have he : n = 45 := by omega
              subst n; exact case45 ⟨p, by omega⟩
            · have he : n = 46 := by omega
              subst n; exact case46 ⟨p, by omega⟩
  · by_cases h68 : n ≤ 68
    · by_cases h57 : n ≤ 57
      · by_cases h52 : n ≤ 52
        · by_cases h49 : n ≤ 49
          · by_cases h48 : n ≤ 48
            · by_cases h47 : n ≤ 47
              · have he : n = 47 := by omega
                subst n; exact case47 ⟨p, by omega⟩
              · have he : n = 48 := by omega
                subst n; exact case48 ⟨p, by omega⟩
            · have he : n = 49 := by omega
              subst n; exact case49 ⟨p, by omega⟩
          · by_cases h51 : n ≤ 51
            · by_cases h50 : n ≤ 50
              · have he : n = 50 := by omega
                subst n; exact case50 ⟨p, by omega⟩
              · have he : n = 51 := by omega
                subst n; exact case51 ⟨p, by omega⟩
            · have he : n = 52 := by omega
              subst n; exact case52 ⟨p, by omega⟩
        · by_cases h55 : n ≤ 55
          · by_cases h54 : n ≤ 54
            · by_cases h53 : n ≤ 53
              · have he : n = 53 := by omega
                subst n; exact case53 ⟨p, by omega⟩
              · have he : n = 54 := by omega
                subst n; exact case54 ⟨p, by omega⟩
            · have he : n = 55 := by omega
              subst n; exact case55 ⟨p, by omega⟩
          · by_cases h56 : n ≤ 56
            · have he : n = 56 := by omega
              subst n; exact case56 ⟨p, by omega⟩
            · have he : n = 57 := by omega
              subst n; exact case57 ⟨p, by omega⟩
      · by_cases h63 : n ≤ 63
        · by_cases h60 : n ≤ 60
          · by_cases h59 : n ≤ 59
            · by_cases h58 : n ≤ 58
              · have he : n = 58 := by omega
                subst n; exact case58 ⟨p, by omega⟩
              · have he : n = 59 := by omega
                subst n; exact case59 ⟨p, by omega⟩
            · have he : n = 60 := by omega
              subst n; exact case60 ⟨p, by omega⟩
          · by_cases h62 : n ≤ 62
            · by_cases h61 : n ≤ 61
              · have he : n = 61 := by omega
                subst n; exact case61 ⟨p, by omega⟩
              · have he : n = 62 := by omega
                subst n; exact case62 ⟨p, by omega⟩
            · have he : n = 63 := by omega
              subst n; exact case63 ⟨p, by omega⟩
        · by_cases h66 : n ≤ 66
          · by_cases h65 : n ≤ 65
            · by_cases h64 : n ≤ 64
              · have he : n = 64 := by omega
                subst n; exact case64 ⟨p, by omega⟩
              · have he : n = 65 := by omega
                subst n; exact case65 ⟨p, by omega⟩
            · have he : n = 66 := by omega
              subst n; exact case66 ⟨p, by omega⟩
          · by_cases h67 : n ≤ 67
            · have he : n = 67 := by omega
              subst n; exact case67 ⟨p, by omega⟩
            · have he : n = 68 := by omega
              subst n; exact case68 ⟨p, by omega⟩
    · by_cases h79 : n ≤ 79
      · by_cases h74 : n ≤ 74
        · by_cases h71 : n ≤ 71
          · by_cases h70 : n ≤ 70
            · by_cases h69 : n ≤ 69
              · have he : n = 69 := by omega
                subst n; exact case69 ⟨p, by omega⟩
              · have he : n = 70 := by omega
                subst n; exact case70 ⟨p, by omega⟩
            · have he : n = 71 := by omega
              subst n; exact case71 ⟨p, by omega⟩
          · by_cases h73 : n ≤ 73
            · by_cases h72 : n ≤ 72
              · have he : n = 72 := by omega
                subst n; exact case72 ⟨p, by omega⟩
              · have he : n = 73 := by omega
                subst n; exact case73 ⟨p, by omega⟩
            · have he : n = 74 := by omega
              subst n; exact case74 ⟨p, by omega⟩
        · by_cases h77 : n ≤ 77
          · by_cases h76 : n ≤ 76
            · by_cases h75 : n ≤ 75
              · have he : n = 75 := by omega
                subst n; exact case75 ⟨p, by omega⟩
              · have he : n = 76 := by omega
                subst n; exact case76 ⟨p, by omega⟩
            · have he : n = 77 := by omega
              subst n; exact case77 ⟨p, by omega⟩
          · by_cases h78 : n ≤ 78
            · have he : n = 78 := by omega
              subst n; exact case78 ⟨p, by omega⟩
            · have he : n = 79 := by omega
              subst n; exact case79 ⟨p, by omega⟩
      · by_cases h85 : n ≤ 85
        · by_cases h82 : n ≤ 82
          · by_cases h81 : n ≤ 81
            · by_cases h80 : n ≤ 80
              · have he : n = 80 := by omega
                subst n; exact case80 ⟨p, by omega⟩
              · have he : n = 81 := by omega
                subst n; exact case81 ⟨p, by omega⟩
            · have he : n = 82 := by omega
              subst n; exact case82 ⟨p, by omega⟩
          · by_cases h84 : n ≤ 84
            · by_cases h83 : n ≤ 83
              · have he : n = 83 := by omega
                subst n; exact case83 ⟨p, by omega⟩
              · have he : n = 84 := by omega
                subst n; exact case84 ⟨p, by omega⟩
            · have he : n = 85 := by omega
              subst n; exact case85 ⟨p, by omega⟩
        · by_cases h88 : n ≤ 88
          · by_cases h87 : n ≤ 87
            · by_cases h86 : n ≤ 86
              · have he : n = 86 := by omega
                subst n; exact case86 ⟨p, by omega⟩
              · have he : n = 87 := by omega
                subst n; exact case87 ⟨p, by omega⟩
            · have he : n = 88 := by omega
              subst n; exact case88 ⟨p, by omega⟩
          · by_cases h89 : n ≤ 89
            · have he : n = 89 := by omega
              subst n; exact case89 ⟨p, by omega⟩
            · have he : n = 90 := by omega
              subst n; exact case90 ⟨p, by omega⟩
#print axioms certSmall

private theorem scale_pos : (0:ℝ) < scale := by norm_num [scale]


private theorem iLow_real (k : ℕ) (hk : k≤180) :
    (iLow k : ℝ)/scale ≤ Real.sqrt k := by
  apply Real.le_sqrt_of_sq_le
  have h := (lowTable_sound ⟨k, by omega⟩).1
  have h' : (iLow k : ℝ)^2 ≤ (k:ℝ)*scale*scale := by exact_mod_cast h
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos scale_pos 2)).2
  nlinarith only [h']

private theorem iHi_real (k : ℕ) (hk : k≤180) :
    Real.sqrt k ≤ (iHi k : ℝ)/scale := by
  apply Real.sqrt_le_iff.2
  refine ⟨div_nonneg (Nat.cast_nonneg _) scale_pos.le, ?_⟩
  have h := (lowTable_sound ⟨k, by omega⟩).2
  have h' : (k:ℝ)*scale*scale < (iHi k : ℝ)^2 := by exact_mod_cast h
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos scale_pos 2)).2
  nlinarith only [h']

set_option maxRecDepth 10000 in
/-- Exact finite range for the degree-sensitive bound, with no graph enumeration. -/
theorem small_exceeds (n p : ℕ) (hn3 : 3≤n) (hn90 : n≤90) (hp : p≤n/2)
    (hn3p : n=3 → p=0) :
    let d := dSmall n p
    let c := Real.sqrt 2*Real.sqrt d/(2+d)
    let b := 1/Real.sqrt d - c/d
    1+(3/2)*(Real.sqrt n-Real.sqrt 2) < ((n:ℝ)-p)*c+p*b := by
  dsimp only
  let d := dSmall n p
  let c : ℝ := Real.sqrt 2*Real.sqrt d/(2+d)
  let b : ℝ := 1/Real.sqrt d - c/d
  let s : ℝ := scale
  let a : ℝ := iLow (2*d)
  let e : ℝ := iHi d
  let u : ℝ := iHi n
  let cl : ℝ := iLow 2
  let cu : ℝ := iHi 2
  have hpn : p ≤ n := by omega
  have hdn : 2≤d := by
    dsimp [d,dSmall]
    split
    · omega
    · omega
  have hdmax : d≤90 := by
    dsimp [d,dSmall]
    split <;> omega
  have hdreal : (2:ℝ)≤d := by exact_mod_cast hdn
  have hd0 : (0:ℝ)<d := by linarith
  have hs : 0<s := scale_pos
  have he : 0<e := by
    dsimp [e, iHi]
    have h : (0:ℝ) ≤ iLow d := Nat.cast_nonneg _
    push_cast
    linarith
  have hD : (0:ℝ)<d+2 := by linarith
  have hD' : (0:ℝ)<2+d := by linarith
  have hcNat : iHi 2 ≤ scale*(d+2) := by
    calc
      iHi 2 ≤ scale*2 := by decide
      _ ≤ _ := Nat.mul_le_mul_left scale (by omega)
  have huNat : 3*iLow 2 ≤ 3*iHi n := by
    apply Nat.mul_le_mul_left
    have hL := iLow_real 2 (by omega)
    have hU := iHi_real n (by omega)
    have hM := Real.sqrt_le_sqrt (show (2:ℝ)≤n by exact_mod_cast (show 2≤n by omega))
    have h := (div_le_div_iff_of_pos_right scale_pos).1 (hL.trans (hM.trans hU))
    exact_mod_cast h
  have hcast : (2:ℝ)*e*((n:ℝ)-p)*a+2*s*p*(s*(d+2)-cu) >
      (3*u-3*cl+2*s)*(d+2)*e := by
    have h := certSmall n p hn3 hn90 hp hn3p
    change 2*iHi d*(n-p)*iLow (2*d)+2*scale*p*(scale*(d+2)-iHi 2) >
      (3*iHi n-3*iLow 2+2*scale)*(d+2)*iHi d at h
    have h' := (Nat.cast_lt (α := ℝ)).2 h
    push_cast [Nat.cast_sub hpn, Nat.cast_sub hcNat, Nat.cast_sub huNat] at h'
    exact h'
  let lc : ℝ := a/(s*(d+2))
  let lb : ℝ := (s*(d+2)-cu)/((d+2)*e)
  let rr : ℝ := (3*u-3*cl+2*s)/(2*s)
  have hnum := mul_pos (mul_pos hs hD) he
  have hrat : rr < ((n:ℝ)-p)*lc+p*lb := by
    dsimp [rr,lc,lb]
    have hid : (((n:ℝ)-p)*(a/(s*(d+2)))+p*((s*(d+2)-cu)/((d+2)*e))) * (2*(s*(d+2)*e)) =
         2*e*((n:ℝ)-p)*a+2*s*p*(s*(d+2)-cu) := by
      field_simp; ring
    have hid' : ((3*u-3*cl+2*s)/(2*s)) * (2*(s*(d+2)*e)) =
         (3*u-3*cl+2*s)*(d+2)*e := by field_simp; ring
    apply lt_of_mul_lt_mul_right _ (show 0≤2*(s*(d+2)*e) by linarith)
    rw [hid,hid']
    exact hcast
  have hclow : lc ≤ c := by
    have h1 := iLow_real (2*d) (by omega)
    push_cast at h1
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at h1
    have h2 := div_le_div_of_nonneg_right h1 hD.le
    dsimp [lc,c,a,s] at h2 ⊢
    rw [add_comm 2]
    rwa [div_div] at h2
  have hhgt : 0< Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hd0
  have hsdr : (Real.sqrt (d:ℝ))^2=d := Real.sq_sqrt hd0.le
  have hb : b=(1-Real.sqrt 2/(2+d))/Real.sqrt d := by
    have hquot : Real.sqrt (d:ℝ)/(d:ℝ) = 1/Real.sqrt d := by
      apply (div_eq_div_iff (ne_of_gt hd0) (ne_of_gt hhgt)).2
      simpa [pow_two] using hsdr
    have hcquot : c/d = (Real.sqrt 2/(2+d))/Real.sqrt d := by
      calc
        c/d = (Real.sqrt 2/(2+d))*(Real.sqrt (d:ℝ)/(d:ℝ)) := by dsimp [c]; ring
        _ = _ := by rw [hquot]; ring
    dsimp [b]
    rw [hcquot]
    ring
  have hnum_order : 1-cu/(s*(d+2)) ≤ 1-Real.sqrt 2/(2+d) := by
    have h1 := div_le_div_of_nonneg_right (iHi_real 2 (by omega)) hD'.le
    apply sub_le_sub_left
    dsimp [cu,s]
    simpa only [Nat.cast_ofNat, div_div, add_comm (2:ℝ) (d:ℝ)] using h1
  have hnum_nn : 0 ≤ 1-cu/(s*(d+2)) := by
    have hN := (Nat.cast_le (α := ℝ)).2 hcNat
    push_cast at hN
    have : cu ≤ s*(d+2) := hN
    have hh' := (div_le_iff₀ (mul_pos hs hD)).2 (by simpa using this : cu ≤ 1*(s*(d+2)))
    linarith
  have hblower : lb ≤ b := by
    rw [hb]
    have hlid : lb=(1-cu/(s*(d+2)))/(e/s) := by
      dsimp [lb]
      field_simp
      ring
    rw [hlid]
    have hb0 : 0 < e/s := div_pos he hs
    calc
      _ ≤ (1-cu/(s*(d+2)))/Real.sqrt d :=
        div_le_div_of_nonneg_left hnum_nn hhgt (iHi_real d (by omega))
      _ ≤ _ := div_le_div_of_nonneg_right hnum_order hhgt.le
  have hrr : 1+(3/2)*(Real.sqrt n-Real.sqrt 2) ≤ rr := by
    have hU := iHi_real n (by omega)
    have hL := iLow_real 2 (by omega)
    have hid : rr = 1+(3/2)*(u/s-cl/s) := by
      dsimp [rr]; field_simp; ring
    rw [hid]
    change Real.sqrt n ≤ u/s at hU
    change cl/s ≤ Real.sqrt 2 at hL
    linarith only [hU,hL]
  have hm₁ := mul_le_mul_of_nonneg_left hclow (sub_nonneg.mpr (by exact_mod_cast hpn : (p:ℝ)≤n))
  have hm₂ := mul_le_mul_of_nonneg_left hblower (Nat.cast_nonneg (α:=ℝ) p)
  exact (hrr.trans_lt hrat).trans_le (add_le_add hm₁ hm₂)

#print axioms small_exceeds
end CazenaveRank
