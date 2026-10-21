#!/bin/bash
# CLOUD-MATH-3 report: each module's main theorems and definitions as they stand, by stmts.py.
: "${EVD:?}" "${REPO:?}"
S=$EVD/scripts/stmts.py
cd "$REPO" || exit 99
echo "### 113, ClassicalLean/Analysis/SubgradientMethod.lean"; python3 -I $S ClassicalLean/Analysis/SubgradientMethod.lean min_sub_le_of_subgradient
echo "### 121, ClassicalLean/Probability/EfronStein.lean"; python3 -I $S ClassicalLean/Probability/EfronStein.lean wmean wvar weight expect variance coordVar variance_le_sum_variance_coord variance_le_sum_sq_div_four
echo "### 130, ClassicalLean/InformationTheory/ChannelCapacity.lean"; python3 -I $S ClassicalLean/InformationTheory/ChannelCapacity.lean mutualInfo_bsc_le mutualInfo_bsc_half
echo "### 124, ClassicalLean/Probability/BernsteinInequality.lean"; python3 -I $S ClassicalLean/Probability/BernsteinInequality.lean measureReal_sum_ge_le_bernstein
echo "### 126, ClassicalLean/Probability/OrderStatistics.lean"; python3 -I $S ClassicalLean/Probability/OrderStatistics.lean orderStat measureReal_orderStat_le
