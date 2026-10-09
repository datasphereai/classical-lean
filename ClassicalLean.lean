/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Algebra.CompanionMatrix
import ClassicalLean.Analysis.GeneralGrowth
import ClassicalLean.Analysis.LogDrag
import ClassicalLean.Analysis.LogGrowthRate
import ClassicalLean.Analysis.RepeatedFees
import ClassicalLean.Analysis.LogGrowthRobustness
import ClassicalLean.Combinatorics.AlgebraicGeneratingFunction
import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction
import ClassicalLean.Geometry.Helix
import ClassicalLean.Geometry.Hopf
import ClassicalLean.Geometry.S3Quaternion
import ClassicalLean.Geometry.SU2SO3
import ClassicalLean.Geometry.Spectral3x3
import ClassicalLean.GoldenRatio.Characterisations
import ClassicalLean.InformationTheory.Channel
import ClassicalLean.InformationTheory.Entropy
import ClassicalLean.InformationTheory.MutualInformation
import ClassicalLean.Logic.PredicateStack
import ClassicalLean.NumberTheory.BiquadraticDiscriminant
import ClassicalLean.NumberTheory.Catalan
import ClassicalLean.NumberTheory.CompositumDiscriminant
import ClassicalLean.NumberTheory.EuclidSteps
import ClassicalLean.NumberTheory.FactorialPart
import ClassicalLean.NumberTheory.Jacobsthal
import ClassicalLean.NumberTheory.Lucas
import ClassicalLean.NumberTheory.LucasCompanion
import ClassicalLean.NumberTheory.LucasApparition
import ClassicalLean.NumberTheory.LucasSequence
import ClassicalLean.NumberTheory.LucasSequenceCases
import ClassicalLean.NumberTheory.LucasSequenceGeneratingFunction
import ClassicalLean.NumberTheory.Mersenne
import ClassicalLean.NumberTheory.MersenneFactorialPart
import ClassicalLean.NumberTheory.MersenneOrder
import ClassicalLean.NumberTheory.NacciTrace
import ClassicalLean.NumberTheory.Pell
import ClassicalLean.NumberTheory.PowerSumCases
import ClassicalLean.NumberTheory.PrimitiveDivisor
import ClassicalLean.NumberTheory.Tribonacci
import ClassicalLean.NumberTheory.Wolstenholme
import ClassicalLean.NumberTheory.Zsigmondy
import ClassicalLean.NumberTheory.ZsigmondyPowSubPow
import ClassicalLean.Order.Superadditive
import ClassicalLean.Order.Tolerance
import ClassicalLean.Probability.DependentSampleMean
import ClassicalLean.Probability.FairGame
import ClassicalLean.Probability.MaximalInequality
import ClassicalLean.Probability.SampleMean
import ClassicalLean.Probability.TwoVariableMix
import ClassicalLean.Simplex.Basic
import ClassicalLean.Simplex.CrossEntropy
import ClassicalLean.Simplex.DesignConstants
import ClassicalLean.Simplex.FisherRao
import ClassicalLean.Simplex.Gibbs
import ClassicalLean.Simplex.Hessian
import ClassicalLean.Simplex.Involution
import ClassicalLean.Simplex.LogSumExp
import ClassicalLean.Simplex.Ordered
import ClassicalLean.Simplex.SecondOrder
import ClassicalLean.Simplex.Symmetry
import ClassicalLean.Simplex.Temperature
import ClassicalLean.Statistics.CramerRao
import ClassicalLean.Statistics.FrischWaughLovell
import ClassicalLean.Statistics.GaussMarkov
import ClassicalLean.Statistics.ResidualVariance
import ClassicalLean.Probability.RelativeEntropyGrowth
import ClassicalLean.Analysis.MinimumQuadraticForm
import ClassicalLean.Probability.FirstOrderRecursion
import ClassicalLean.Probability.StepUpProcedure
import ClassicalLean.Probability.RuinBound
import ClassicalLean.Analysis.GrowthMaximiser
import ClassicalLean.Probability.LikelihoodScore
import ClassicalLean.Probability.NoEdgeWealth
import ClassicalLean.Probability.EValueStepUp
import ClassicalLean.Probability.CovarianceDirections
import ClassicalLean.Probability.TwoStateChain
import ClassicalLean.Probability.LinearPrediction
import ClassicalLean.InformationTheory.SignalGrowth
import ClassicalLean.Analysis.RoundingError
import ClassicalLean.Probability.EdgeGrowth
import ClassicalLean.Probability.ScoreLookahead
import ClassicalLean.Probability.EffectiveSampleSize
import ClassicalLean.Analysis.UniversalMixture
import ClassicalLean.Analysis.HermiteHadamard
import ClassicalLean.Statistics.GeneralizedLeastSquares
import ClassicalLean.InformationTheory.SourceCoding
import ClassicalLean.Analysis.GradientDescent
import ClassicalLean.Analysis.ExponentialWeights
import ClassicalLean.Statistics.RaoBlackwell
import ClassicalLean.Statistics.Cochran
import ClassicalLean.Probability.YuleWalker
import ClassicalLean.Probability.MovingAverage
import ClassicalLean.Probability.TailBounds
import ClassicalLean.Analysis.ConditionNumber
import ClassicalLean.Analysis.LinearODE
import ClassicalLean.Statistics.Sufficiency
import ClassicalLean.Analysis.EulerMethod
import ClassicalLean.Analysis.JacobiIteration
import ClassicalLean.Analysis.NewtonMethod
import ClassicalLean.Probability.FiniteChain
import ClassicalLean.InformationTheory.Fano
import ClassicalLean.Algebra.HadamardInequality

/-!
# ClassicalLean

Aggregator: imports every shipped module and nothing else.

There is no `ClassicalLean/Open/` any more. It held the harvest's one genuinely open problem,
whose last hole was closed; the material is now `NumberTheory/MersenneFactorialPart.lean`, in the
shipped library and gated like everything else. **This library contains no `sorry`.** The policy
that permits one under `Open/` stands in `tools/check_sorry.py` for the next open problem.

Every module above is required to pass four gates, all runnable and all shown to fail on a
deliberately broken input before being trusted on a real one:

* `tools/AxiomGate.lean`        — every theorem's kernel dependency is a subset of
                                  `{propext, Classical.choice, Quot.sound}`, plus any
                                  named scoped exception
* `tools/VacuityGate.lean`      — no theorem's conclusion is `True` or one of its own hypotheses
* `tools/check_sorry.py`        — no `sorry`, `admit`, `native_decide` or bare `axiom`
                                  outside the directories that permit them
* `tools/banned_vocab_scan.py`  — no retired project vocabulary, in code or in prose

The Authors line credits Claude (Anthropic) alongside the copyright holder; how the library was
written and ported is recorded in `records/`.
-/
