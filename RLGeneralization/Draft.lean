-- RLGeneralization.Draft: frontier modules excluded from the trusted root.
--
-- These files build, but contain vacuous theorems, thin wrappers,
-- or pure hypothesis-forwarding, so they are not part of the
-- trusted benchmark target.

-- Bellman rank and GOLF (has vacuous theorem)
import RLGeneralization.BilinearRank.Basic

-- Offline RL function approximation (hypothesis-forwarding wrappers)
import RLGeneralization.OfflineRL.FunctionApprox
-- POMDP belief MDP (thin wrappers over POMDP module)
import RLGeneralization.MDP.POmdpBeliefMDP

-- ───────────────────────────────────────────────────────────────
-- Orphan modules: compile but not yet promoted to root
-- ───────────────────────────────────────────────────────────────

-- MDP
import RLGeneralization.MDP.AverageRewardReduction
import RLGeneralization.MDP.Coverability
import RLGeneralization.MDP.ReferenceAdvantage
import RLGeneralization.MDP.ValueDecomposition
import RLGeneralization.MDP.VarianceSimulation
import RLGeneralization.MDP.WeaklyCommunicating

-- Generalization
import RLGeneralization.Generalization.BradleyTerry
import RLGeneralization.Generalization.KLProperties
import RLGeneralization.Generalization.TVProperties

-- PolicyOptimization
import RLGeneralization.PolicyOptimization.DensityRatio
import RLGeneralization.PolicyOptimization.ImplicitQ
import RLGeneralization.PolicyOptimization.KLRegularized
import RLGeneralization.PolicyOptimization.PolicySmooth

-- LinearMDP
import RLGeneralization.LinearMDP.InverseCovariance
import RLGeneralization.LinearMDP.InformationGain

-- Optimization
import RLGeneralization.Optimization.MirrorDescent

-- Concentration
import RLGeneralization.Concentration.ConfidenceSequence
import RLGeneralization.Concentration.BernsteinSample
import RLGeneralization.Concentration.ChiSquared
import RLGeneralization.Concentration.FDivergence
import RLGeneralization.Concentration.Freedman
import RLGeneralization.Concentration.Hellinger
import RLGeneralization.Concentration.ImportanceSamplingGeneral
import RLGeneralization.Concentration.MarkovChain
import RLGeneralization.Concentration.SelfBounding
import RLGeneralization.Concentration.TotalVariance
import RLGeneralization.Concentration.TriangularDiscrimination

-- OfflineRL
import RLGeneralization.OfflineRL.LeaveOneOut
import RLGeneralization.OfflineRL.PessimisticVI
import RLGeneralization.OfflineRL.RobustShrinkage

-- Test
import RLGeneralization.Test.ConcreteExample

-- ───────────────────────────────────────────────────────────────
-- Library expansion: standalone building-block lemmas
-- ───────────────────────────────────────────────────────────────

-- Concentration
import RLGeneralization.Concentration.AbelSummation
import RLGeneralization.Concentration.BiasVariance
import RLGeneralization.Concentration.DiscreteGronwall
import RLGeneralization.Concentration.ExpInequality
import RLGeneralization.Concentration.GibbsVariational
import RLGeneralization.Concentration.HarmonicSum
import RLGeneralization.Concentration.LogLinear
import RLGeneralization.Concentration.LogSumExp
import RLGeneralization.Concentration.ProdOneAdd
import RLGeneralization.Concentration.ProdOneSub
import RLGeneralization.Concentration.Softplus
import RLGeneralization.Concentration.L1L2Bound
import RLGeneralization.Concentration.WeightedCauchySchwarz
import RLGeneralization.Concentration.InvOneSub
import RLGeneralization.Concentration.LogSqrt
import RLGeneralization.Concentration.SqSubBound
import RLGeneralization.Concentration.HarmonicBound
import RLGeneralization.Concentration.MulExpBound
import RLGeneralization.Concentration.SqConvex
import RLGeneralization.Concentration.EntropyBound
import RLGeneralization.Concentration.Popoviciu
import RLGeneralization.Concentration.ExpJensen
import RLGeneralization.Concentration.AmHm
import RLGeneralization.Concentration.ExpQuadUpper
import RLGeneralization.Concentration.SqrtSubadditive
import RLGeneralization.Concentration.SumInvSq
import RLGeneralization.Concentration.YoungEpsilon

-- MDP
import RLGeneralization.MDP.ContractionIterate
import RLGeneralization.MDP.DiscountedSum

-- Optimization
import RLGeneralization.Optimization.AffineContraction
import RLGeneralization.Optimization.GeometricDecay
import RLGeneralization.Optimization.LearningRateOpt
import RLGeneralization.Optimization.OnlineToBatch
import RLGeneralization.Optimization.QuadraticMinBound
import RLGeneralization.Optimization.WeightedSqSumEqZeroIff

-- LinearMDP
import RLGeneralization.LinearMDP.EpochCountBound
import RLGeneralization.LinearMDP.SqrtLipschitz
