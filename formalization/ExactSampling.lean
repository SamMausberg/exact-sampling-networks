import ExactSampling.Attention.AttentionHeads
import ExactSampling.Attention.CertifiedReplay
import ExactSampling.Attention.DynamicIndex
import ExactSampling.Attention.FiniteQueryLists
import ExactSampling.Attention.FixedRank
import ExactSampling.Attention.ImplicitRankOne
import ExactSampling.Attention.IndexedLower
import ExactSampling.Attention.MomentDecoder
import ExactSampling.Checkpoint.CheckpointCertificates
import ExactSampling.Conference.Chart
import ExactSampling.Conference.FixedModel
import ExactSampling.Conference.GridIndex
import ExactSampling.Conference.Moments
import ExactSampling.Conference.RejectionLoop
import ExactSampling.Conference.Replay
import ExactSampling.Conference.ReplaySchedule
import ExactSampling.Conference.RowFactory
import ExactSampling.Conference.SearchObstruction
import ExactSampling.Conference.Stability
import ExactSampling.Critical.ColumnEnvelope
import ExactSampling.Critical.ColumnEnvelopeTilting
import ExactSampling.Critical.CriticalScoreCeiling
import ExactSampling.Critical.FixedRankBatching
import ExactSampling.Critical.NewBottleneck
import ExactSampling.Critical.NewCriticalLemmas
import ExactSampling.Critical.NewSignedBottleneck
import ExactSampling.Critical.RankTwoBernstein
import ExactSampling.Instance.BooleanGates
import ExactSampling.Instance.QueryFlow
import ExactSampling.Instance.RelayGates
import ExactSampling.Instance.ScoreCertificate
import ExactSampling.Instance.WeightObstructions
import ExactSampling.Links.ChartBasis
import ExactSampling.Links.ConferenceDecoder
import ExactSampling.Links.ConferenceGrid
import ExactSampling.Links.InstanceCost
import ExactSampling.Links.ResidualChain
import ExactSampling.Links.TanhChain
import ExactSampling.Links.ZeroBiasChain
import ExactSampling.Lower.IntegerScore
import ExactSampling.Lower.TranscriptLowerBounds
import ExactSampling.Normalization.AdditiveNormalizedGain
import ExactSampling.Normalization.FeedForward
import ExactSampling.Normalization.GaussianRMS
import ExactSampling.Normalization.PreNormAdditive
import ExactSampling.Normalization.PreNormDepthLower
import ExactSampling.Normalization.RMSContextLaw
import ExactSampling.Normalization.RMSFloor
import ExactSampling.Normalization.ScalarRMS
import ExactSampling.Residual.CriticalCounts
import ExactSampling.Residual.FusedFactory
import ExactSampling.Residual.Potential
import ExactSampling.Residual.ResidualDepth
import ExactSampling.Residual.ResidualSampling
import ExactSampling.Stopping.ExactnessStopping
import ExactSampling.Stopping.StoppedCost
import ExactSampling.Tanh.MajorityArity
import ExactSampling.Tanh.ProductArity
import ExactSampling.Tanh.ProductAritySampler
import ExactSampling.Tanh.SharpRates
import ExactSampling.Tanh.SoftmaxHead
import ExactSampling.Tanh.StoppedWork
import ExactSampling.Tanh.TanhFactory

/-!
# ExactSampling

Lean 4 formalization of "Exact Sampling from Neural Networks: Depth, Attention, and Decoding"
(Samuel Mausberg). This root file imports every module of the library. See `README.md` for
the scope of each module and `PAPER_MAP.md` for the paper label behind each theorem.
-/
