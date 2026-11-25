import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Split the fixed `G11` counting step at the sharp lower bound on junk gates. -/
theorem PEqualNP.Outside.R_meta_6768_743
    (exactTwo :
      let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : Circuit),
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).card = 2 →
        C.size ≤ 21 →
        2 * (PEqualNP.TopForm.centreless G C).card +
            (PEqualNP.TopForm.junk G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
          2 * (PEqualNP.TopForm.Ustar G C).card →
        (∀ (v : Fin 11), v.val < 4 →
          (∀ k < C.size, v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or) ∧
          ∀ i j k : ℕ, i < j → j < k → k < C.size →
            v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs →
            v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
            v.val ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) →
        ∃ (v : Fin 11), v.val < 4 ∧
          let erasable : ℕ → Prop := fun k =>
            ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false →
              PEqualNP.ReadTwo.wval C x (11 + k) = PEqualNP.ReadTwo.wval C x w
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧
            erasable i ∧ erasable j ∧ erasable k)
    (threeOrMore :
      let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : Circuit),
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        3 ≤ (PEqualNP.TopForm.junk G C).card →
        C.size ≤ 21 →
        2 * (PEqualNP.TopForm.centreless G C).card +
            (PEqualNP.TopForm.junk G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
          2 * (PEqualNP.TopForm.Ustar G C).card →
        (∀ (v : Fin 11), v.val < 4 →
          (∀ k < C.size, v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or) ∧
          ∀ i j k : ℕ, i < j → j < k → k < C.size →
            v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs →
            v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
            v.val ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) →
        ∃ (v : Fin 11), v.val < 4 ∧
          let erasable : ℕ → Prop := fun k =>
            ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false →
              PEqualNP.ReadTwo.wval C x (11 + k) = PEqualNP.ReadTwo.wval C x w
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧
            erasable i ∧ erasable j ∧ erasable k) :
    let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ (C : Circuit),
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      C.size ≤ 21 →
      2 * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
        2 * (PEqualNP.TopForm.Ustar G C).card →
      (∀ (v : Fin 11), v.val < 4 →
        (∀ k < C.size, v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or) ∧
        ∀ i j k : ℕ, i < j → j < k → k < C.size →
          v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs →
          v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
          v.val ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) →
      ∃ (v : Fin 11), v.val < 4 ∧
        let erasable : ℕ → Prop := fun k =>
          ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false →
            PEqualNP.ReadTwo.wval C x (11 + k) = PEqualNP.ReadTwo.wval C x w
        ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧
          erasable i ∧ erasable j ∧ erasable k := by
  dsimp only at exactTwo threeOrMore ⊢
  intro C hLeast hTop hTwo hSize hCount hReads
  by_cases hEq : (PEqualNP.TopForm.junk
      (PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) C).card = 2
  · exact exactTwo C hLeast hTop hEq hSize hCount hReads
  · exact threeOrMore C hLeast hTop (by omega) hSize hCount hReads
