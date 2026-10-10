import Lake
open Lake DSL

package sorting_depth_lower_best where
  packagesDir := "../../.lake/packages"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, true⟩
  ]

require legacy_upper from "../../upper-bound/alternatives/legacy"

@[default_target]
lean_lib LowerBest where
  roots := #[
    `AKS.Bounds.Kahale,
    `AKS.Bounds.KahaleAsymptotic,
    `AKS.Bounds.KahaleAxioms,
    `AKS.Bounds.Minimum,
    `AKS.Kahale.ApproxSelection,
    `AKS.Kahale.BinomialPotential,
    `AKS.Kahale.Certificates,
    `AKS.Kahale.Fanout,
    `AKS.Kahale.FibonacciBound,
    `AKS.Kahale.GreedyLayers,
    `AKS.Kahale.LayeredBound,
    `AKS.Kahale.LayerPotential,
    `AKS.Kahale.LogRemainder,
    `AKS.Kahale.NetworkBound,
    `AKS.Kahale.RankInputs,
    `AKS.Kahale.RankInterval,
    `AKS.Kahale.SelectionCounting,
    `AKS.Kahale.TimedExecution
  ]
