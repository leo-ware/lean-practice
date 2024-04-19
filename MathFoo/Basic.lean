
variable {p : Prop}
variable {q : Prop}

theorem my_mt (h₀: p → q) (h₁: ¬ q): ¬ p :=
  fun (h₂ : p) =>
  show False from h₁ (h₀ h₂)

theorem my_and_swap: p ∧ q ↔ q ∧ p :=
  ⟨
    λ (h₀ : p ∧ q) =>
      ⟨ h₀.right, h₀.left ⟩,
    λ (h₁ : q ∧ p) =>
      ⟨ h₁.right, h₁.left ⟩
  ⟩

theorem or_dist (naob: ¬ (a ∨ b)): ¬ a ∧ ¬ b :=
    ⟨
      λ (pa: a) => naob (Or.inl pa),
      λ (pb: b) => naob (Or.inr pb)
    ⟩

-- theorem nnp_imp_em (dn: ∀p, ¬¬p → p): q ∨ ¬q :=
--   suffices dnem: ¬¬(q ∨ ¬ q) from dn dnem
--   show dnem from
--     λ (nem : ¬(p ∨ ¬ p)) =>
--       have (npannp: ¬ p ∧ ¬¬p) := or_dist nem
--       have (np: ¬ p) := npannp.left
--       have (nnp: ¬ ¬ p) := npannp.right
--       show False from nnp np
