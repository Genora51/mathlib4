/-
Copyright (c) 2023 Geno Racklin Asher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geno Racklin Asher
-/
import Mathlib

/-!
# Burnside's theorem

This file contains a proof of **Burnside's theorem**, which states that a group `G` of order
`p^a * q^b`, for distinct primes `p` and `q`, is not simple (assuming `a + b ≥ 2`).

## Main results

* `not_simple_of_card_paqb`: A group of order `p^a * q^b` is not simple.

## TODO

Extend the statement of the theorem to "`G` is solvable".
-/

variable {G : Type _} [Group G] [Fintype G]
variable {p q r a b : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]

theorem not_simple_of_ccl_card_prime_pow (hnabelian : ¬∀ (g h : G), g * h = h * g)
  {g : G} (hg : g ≠ 1) (hccl : Nat.card (MulAction.orbit (ConjAct G) g) = p ^ r)
  : ¬IsSimpleGroup G := by
  sorry
--   -- Suppose for contradiction that G is simple
--   intro hG
--   -- Let chi be a nontrivial irreducible character of G
--   let ⟨chi, hchi⟩ := _
--   have : |chi x| < chi e := by sorry
--   have : p ∣ chi e ∨ chi g = 0 := by sorry
--   -- By column orthogonality, find a contradiction

lemma one_le_or_zero_le (hab : 1 < a + b) : 1 < b ∨ 0 < a := by
  cases a
  · rw [Nat.zero_add] at hab
    apply Or.inl hab
  · apply Or.inr
    apply Nat.succ_pos

section Burnside

theorem not_simple_of_abelian_card_paqb
 (hab : 1 < a + b) (hb : 0 < b) (hg : Fintype.card G = p ^ a * q ^ b)
 (habelian : ∀ (g h : G), g * h = h * g) : ¬IsSimpleGroup G := by
  let ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime q (n := 1) (
    show q^1 ∣ Nat.card G by calc q^1
    _ = q := pow_one q
    _ ∣ q^b := dvd_pow_self _ (pos_iff_ne_zero.mp hb)
    _ ∣ Fintype.card G := by simp [hg]
    _ = Nat.card G := by exact Fintype.card_eq_nat_card
  )
  rw [pow_one] at hH
  change ¬IsSimpleGroup G
  intro hG
  have : H.Normal := ⟨by simp [habelian]⟩
  -- show H is neither trivial nor G
  apply absurd
  · apply IsSimpleGroup.eq_bot_or_eq_top_of_normal H this
  apply not_or.mpr
  constructor
  -- show H is not trivial by cardinality (q ≠ 1)
  · intro hHtriv
    have : Nat.card H = 1 := by
      rw [hHtriv, Subgroup.card_bot]
    have : Nat.card H ≠ 1 := by
      rw [hH]
      apply Nat.Prime.ne_one hq.elim
    contradiction
  -- show H is not G by cardinality (q ≠ p^a * q^b)
  · intro hHT
    have : Nat.card (⊤: Subgroup G) = Fintype.card G := by
      simp
    have hpaqb : Nat.card H = p^a * q^b := by
      rw [hHT, this, hg]
    have : p^a * q^b ≠ q := by
      have h0qb : 0 < q^b := by
        apply pow_pos (Nat.Prime.pos hq.elim) b
      apply Or.elim (one_le_or_zero_le hab)
      · intro h1
        have h1pa : 1 ≤ p^a := by
          apply one_le_pow_of_one_le'
          exact Nat.Prime.pos hp.elim
        have : q < p^a * q^b := calc q
          _ = q^1 := by ring
          _ < q^b := pow_lt_pow_right₀ (Nat.Prime.one_lt hq.elim) h1
          _ ≤ p^a * q^b := by
            rw [Nat.mul_comm]
            apply (le_mul_iff_one_le_right h0qb).mpr
            exact h1pa
        apply ne_of_gt this
      · intro h0
        have : q < p^a * q^b := calc q
          _ = q^1 := by ring
          _ ≤ q^b := pow_le_pow_right₀
            (by have := Nat.Prime.two_le hq.elim; linarith) (Nat.one_le_of_lt hb)
          _ < p^a * q^b := by
            rw [Nat.mul_comm]
            have : 1 < p^a := by
              apply one_lt_pow'
              · exact Nat.Prime.one_lt hp.elim
              · exact ne_of_gt h0
            apply lt_mul_right h0qb this
        apply ne_of_gt this
    have : Nat.card H ≠ q := by
      rw [hpaqb]
      apply this
    contradiction

theorem not_simple_of_not_abelian_card_paqb
  (hb : 0 < b) (hg : Fintype.card G = p ^ a * q ^ b)
  (hnabelian : ¬∀ (g h : G), g * h = h * g) : ¬IsSimpleGroup G := by
  -- Let Q be a Sylow q-subgroup of G
  let ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime q (show q^b ∣ Nat.card G by simp [hg])
  have : Nontrivial Q := by
    have := Fintype.ofFinite Q
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [←Nat.card_eq_fintype_card, hQ]
    apply Nat.one_lt_pow
    · exact Nat.ne_zero_of_lt hb
    exact Nat.Prime.one_lt hq.elim
  -- Q is a nontrivial p-group, so its center is nontrivial
  have := IsPGroup.center_nontrivial (IsPGroup.of_card hQ)
  -- Let x be a nontrivial element of the center of Q
  let ⟨x, hx⟩ : ∃ (x : Subgroup.center Q), x ≠ 1 := exists_ne _
  let X := Subgroup.closure {x.val.val}
  let CGx := Subgroup.centralizer (G := G) X
  have hXZQ : X ≤ (Subgroup.center Q).map Q.subtype := by
    apply Iff.mpr
    · apply Subgroup.closure_le
    intro z hz
    rw [hz]
    apply Subgroup.mem_map.mpr
    use x.val
    simp
  -- Q is contained in C_G(x)
  have hQCG : Q ≤ CGx := by
    intro q hq
    intro z hz
    have : z ∈ (Subgroup.center Q).map Q.subtype := by
      apply hXZQ
      apply hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp this
    obtain ⟨q', hq'⟩ : ∃ (q' : Q), ↑q' = q := CanLift.prf q hq
    simp
    have : q' * z' = z' * q' := by
      apply Subgroup.mem_center_iff.mp
      apply hz'
    rw [←hq', ←Subgroup.coe_mul, ←this, Subgroup.coe_mul]
  -- So we apply orbit-stabilizer to show |ccl(x)| divides |G/Q| = p^a
  have hCGStab : CGx = MulAction.stabilizer (ConjAct G) (x.val.val) := by
    calc CGx = Subgroup.centralizer (Subgroup.closure {x.val.val}) := rfl
      _ = Subgroup.centralizer
        (Subgroup.zpowers (ConjAct.toConjAct (x : G)) : Set (ConjAct G)) := by
        rw [Subgroup.zpowers_eq_closure]
        rfl
      _ = MulAction.stabilizer (ConjAct G) (x.val.val) := by
        rw [←ConjAct.stabilizer_eq_centralizer]
  let cclx := MulAction.orbit (ConjAct G) (x.val.val)
  have : Nat.card cclx ∣ p^a := by
    have := Fintype.ofFinite cclx
    have := Fintype.ofFinite <| MulAction.stabilizer (ConjAct G) (x.val.val)
    have := Fintype.ofFinite ↥CGx
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (x.val.val)
    have hCG': Fintype.card CGx = Fintype.card (MulAction.stabilizer (ConjAct G) x.val.val) := by
      apply Fintype.card_congr'
      rw [hCGStab]
      rfl
    rw [←hCG'] at h
    have : Nat.card Q ∣ Nat.card CGx := Subgroup.card_dvd_of_le hQCG
    rw [hQ] at this
    apply Iff.mp
    · apply Nat.mul_dvd_mul_iff_right
      · calc 0 < 1 := Nat.one_pos
        _ ≤ q^b := Nat.one_le_pow b q (Nat.Prime.pos hq.elim)
    · calc Nat.card cclx * q^b
        _ ∣ Nat.card cclx * Nat.card CGx := by
          apply Nat.mul_dvd_mul_left; exact this
        _ = Fintype.card cclx * Fintype.card CGx := by simp
        _ = Fintype.card G := h
        _ = p^a * q^b := hg
  -- ccl(x) has size a power of p, so apply a lemma to conclude
  have ⟨r, hr⟩ : ∃ r, r ≤ a ∧ Nat.card cclx = p^r := by
    apply (Nat.dvd_prime_pow hp.elim).mp
    exact this
  apply not_simple_of_ccl_card_prime_pow (p := p)
  · exact hnabelian
  · change (x.val.val ≠ 1)
    · intro h
      apply hx
      apply Subtype.eq
      apply Subtype.eq
      exact h
  · exact hr.right

/-- **Burnside's theorem**. A group `G` of order `p^a * q^b`,
for distinct primes `p` and `q`, is not simple (assuming `a + b ≥ 2`). -/
theorem not_simple_of_card_paqb (hab : 1 < a + b) (hb : 0 < b)
  (hg : Fintype.card G = p ^ a * q ^ b) : ¬IsSimpleGroup G := by
  by_cases habel : (∀ (g h : G), g * h = h * g)
  -- have hComm : CommGroup G := ⟨habelian⟩
  · apply not_simple_of_abelian_card_paqb hab hb hg habel
  · apply not_simple_of_not_abelian_card_paqb hb hg habel

end Burnside
