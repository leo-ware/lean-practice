variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
⟨
  λ (pq: p ∧ q) => ⟨ pq.right, pq.left ⟩,
  λ (qp: q ∧ p) => ⟨ qp.right, qp.left ⟩
⟩

example: p ∨ q ↔ q ∨ p :=
⟨
  λ (pq: p ∨ q) => Or.elim pq Or.inr Or.inl,
  λ (qp: q ∨ p) => Or.elim qp Or.inr Or.inl
⟩

-- -- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
⟨
  λ (pqr: (p ∧ q) ∧ r) =>
    ⟨ pqr.left.left, ⟨ pqr.left.right, pqr.right ⟩⟩,
  λ (pqr: p ∧ (q ∧ r)) =>
    ⟨ ⟨ pqr.left, pqr.right.left ⟩, pqr.right.right ⟩
⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
⟨
  λ (h₀: (p ∨ q) ∨ r) =>
    Or.elim h₀
      (λ (pq: p ∨ q) => Or.elim pq
        Or.inl
        (λ (hq: q) => Or.inr (Or.inl hq))
        )
      (λ (hr: r) => Or.inr (Or.inr hr)),
  λ (h₁: p ∨ (q ∨ r)) =>
    Or.elim h₁
      (λ (hp: p) => Or.inl (Or.inl hp))
      (λ (qp: q ∨ r) =>
        Or.elim qp
          (λ (hq: q) => Or.inl (Or.inr hq))
          Or.inr)
⟩

-- -- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
⟨
  λ (h₀ : p ∧ (q ∨ r)) =>
    Or.elim h₀.right
      (λ (hq: q) => Or.inl ⟨ h₀.left, hq ⟩ )
      (λ (hr: r) => Or.inr ⟨ h₀.left, hr ⟩ ),
  λ (h₁ : (p ∧ q) ∨ (p ∧ r)) =>
  ⟨
    Or.elim h₁ And.left And.left,
    Or.elim h₁
      (λ (pq: p ∧ q) => Or.inl pq.right)
      (λ (pr: p ∧ r) => Or.inr pr.right)
  ⟩
⟩


-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
-- ⟨
--   λ (h₀: p ∨ (q ∧ r)) => Or.elim h₀
--     (λ (hp: p) => ⟨ Or.inl hp, Or.inl hp ⟩ )
--     (λ (qr: q ∧ r) => ⟨ Or.inr qr.left, Or.inr qr.right ⟩ ),
--   λ (h₁: (p ∨ q) ∧ (p ∨ r)) =>
--     ⟨ sorry
--       sorry,
--       sorry
--       -- Or.elim h₁ Or.left Or.left,
--       -- Or.elim h₁
--       --   (λ (pq: p ∨ q) =>
--       --     Or.elim pq Or.inl (λ hq: q => Or.inr Or.inl hq))
--       --   (λ (pr: p ∨ r) =>
--       --     Or.elim pq Or.inl (λ hr: r => Or.inr Or.inr hr))
--     ⟩
-- ⟩

-- -- other properties
-- example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
-- example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
-- example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
-- example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
-- example : ¬(p ∧ ¬p) := sorry
-- example : p ∧ ¬q → ¬(p → q) := sorry
-- example : ¬p → (p → q) := sorry
-- example : (¬p ∨ q) → (p → q) := sorry
-- example : p ∨ False ↔ p := sorry
-- example : p ∧ False ↔ False := sorry
-- example : (p → q) → (¬q → ¬p) := sorry
