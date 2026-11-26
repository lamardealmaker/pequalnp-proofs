import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4678_742
    (h0 :
      have x1 : Finset (Fin 13) := {0, 1, 3, 9}
      have x2 : (List Bool → Bool) → Prop := fun f =>
        (∀ p l : Fin 13, p - l ∈ x1 →
          f (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun u : Fin 13 => decide (u = l))) = true) ∧
        ∀ Q : Finset (Fin 13), Q.card = 4 →
          (∀ l : Fin 13, (Q.filter fun u => u - l ∈ x1).card ≤ 2) →
          f (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ u ∈ Q, u - l ∉ x1))) = false
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun C s =>
        x2 fun x => C.eval (x ++ [s.any fun i => x.getD i false])
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        ∀ s ∈ ([[], [0], [13], [0, 1]] : List (List ℕ)),
          PEqualNP.MetaComplexity.Monotone2 C → x4 C → x3 C s → 63 ≤ C.size)
    (h1 :
      have x1 : Finset (Fin 13) := {0, 1, 3, 9}
      have x2 : (List Bool → Bool) → Prop := fun f =>
        (∀ p l : Fin 13, p - l ∈ x1 →
          f (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun u : Fin 13 => decide (u = l))) = true) ∧
        ∀ Q : Finset (Fin 13), Q.card = 4 →
          (∀ l : Fin 13, (Q.filter fun u => u - l ∈ x1).card ≤ 2) →
          f (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ u ∈ Q, u - l ∉ x1))) = false
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun C s =>
        x2 fun x => C.eval (x ++ [s.any fun i => x.getD i false])
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        ∀ s ∈ ([[0, 2], [0, 13], [0, 14], [0, 15]] : List (List ℕ)),
          PEqualNP.MetaComplexity.Monotone2 C → x4 C → x3 C s → 63 ≤ C.size)
    (h2 :
      have x1 : Finset (Fin 13) := {0, 1, 3, 9}
      have x2 : (List Bool → Bool) → Prop := fun f =>
        (∀ p l : Fin 13, p - l ∈ x1 →
          f (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun u : Fin 13 => decide (u = l))) = true) ∧
        ∀ Q : Finset (Fin 13), Q.card = 4 →
          (∀ l : Fin 13, (Q.filter fun u => u - l ∈ x1).card ≤ 2) →
          f (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ u ∈ Q, u - l ∉ x1))) = false
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun C s =>
        x2 fun x => C.eval (x ++ [s.any fun i => x.getD i false])
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        ∀ s ∈ ([[0, 17], [0, 20], [13, 14], [13, 15]] : List (List ℕ)),
          PEqualNP.MetaComplexity.Monotone2 C → x4 C → x3 C s → 63 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size := by
  dsimp only at h0 h1 h2 ⊢
  intro C s hs hm ho hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 C [] (by simp) hm ho hp
  · exact h0 C [0] (by simp) hm ho hp
  · exact h0 C [13] (by simp) hm ho hp
  · exact h0 C [0, 1] (by simp) hm ho hp
  · exact h1 C [0, 2] (by simp) hm ho hp
  · exact h1 C [0, 13] (by simp) hm ho hp
  · exact h1 C [0, 14] (by simp) hm ho hp
  · exact h1 C [0, 15] (by simp) hm ho hp
  · exact h2 C [0, 17] (by simp) hm ho hp
  · exact h2 C [0, 20] (by simp) hm ho hp
  · exact h2 C [13, 14] (by simp) hm ho hp
  · exact h2 C [13, 15] (by simp) hm ho hp
