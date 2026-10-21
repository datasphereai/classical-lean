/-- The hypotheses of `mutualInfo_bsc_le` hold together: the crossover probability `ε = 1 / 4`,
inside `[0, 1]` and away from `1 / 2` (where the capacity is `0`), and the input law
`p = (1 / 3, 2 / 3)`, which is not uniform. -/
example := ClassicalLean.InformationTheory.ChannelCapacity.mutualInfo_bsc_le (ε := 1 / 4)
    (p := ![1 / 3, 2 / 3]) (by norm_num) (by norm_num)
    (fun a => by fin_cases a <;> norm_num) (by norm_num [Fin.sum_univ_two])

/-- The hypotheses of `mutualInfo_bsc_half` hold together: the crossover probability
`ε = 1 / 4`, inside `[0, 1]` and away from `1 / 2` (where the capacity is `0`). -/
example := ClassicalLean.InformationTheory.ChannelCapacity.mutualInfo_bsc_half (ε := 1 / 4)
    (by norm_num) (by norm_num)
