/-- The hypotheses of `huffman_optimal` hold together: three symbols (`ι = Fin 3`) with the
weights `p = (1/2, 1/4, 1/4)`, all positive and not all equal, and the two-letter alphabet
`α = Bool`. -/
example := ClassicalLean.InformationTheory.Huffman.huffman_optimal (ι := Fin 3) (α := Bool)
    (p := ![1 / 2, 1 / 4, 1 / 4]) Fintype.card_bool (fun i => by fin_cases i <;> norm_num)
