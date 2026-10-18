import Exploding.Support.SquareGreenOriginLower
import Exploding.Support.CorrectedSourceConsumers
import Exploding.Support.AllHighGeneralizedHypotheses
import Exploding.Support.AllHighPathFilling
import Exploding.Support.WaveApproximationSource
import Exploding.Support.SourceCriterionVacuity
import Exploding.Support.BCDimOne
import Exploding.Support.OmegaErgodic
import Exploding.Support.OmegaTraceSigma
import Exploding.Support.OmegaStationary
import Exploding.Support.RecurrentMeasurable
import Exploding.Support.ExplosiveMeasurable
import Exploding.Support.ArxivBondHoleTailMoments
import Exploding.Support.ArxivActualBondCoreProximity
import Exploding.Support.ArxivBondTranslatedBoxTail
import Exploding.Support.ArxivActualBondOne
import Exploding.Support.PathFillingBarrier
import Exploding.Support.ReductionBoundary
import Exploding.Support.PathFillingDetour
import Exploding.Support.PathFillingNonneg
import Exploding.Support.OmegaCriterionConsumer
import Exploding.MainTheorems
import Exploding.Support.ExplosiveVacuity
import Exploding.Support.ExtFMR
import Exploding.Support.LSProofAux
import Exploding.Support.ExtLSSCountable
import Exploding.Support.ExtMHHoleVolume
import Exploding.Support.ExtSchFinal
import Exploding.Support.ExtSchFLP
import Exploding.Support.PlanarWaveOrder
import Exploding.Support.PlanarWaveBarrier

/-!
# Axioms audit

Building this module prints the axiom dependencies of the 22 proved paper results restated in
`Exploding/MainTheorems.lean`, the sharp planar obstruction remark restated there, and the all-high
endpoint check of Theorem 1.4. Each must report
exactly the three standard foundational axioms of Mathlib: `propext`, `Classical.choice`,
`Quot.sound`.

The registered theorem exports listed here include Theorems 1.2, 1.3, 1.4, 5.1 and 6.1,
Propositions 2.1, 2.2, 3.1, 4.1, 5.1, 7.1, 7.2, 7.3 and 7.5, and Lemmas 2.1 and 3.1 to 3.7.
Their source pins and the remaining gaps in each source are recorded in `ledger/manifest.yaml`.
`python3 tools/check_axioms.py` prints the axiom closure of every registered statement.

No `axiom` is declared in this development.  The seven cited results are stated as
propositions in `Exploding/External/` and taken as explicit hypotheses by the theorems that
use them (see `ASSUMPTIONS.md`), so they never appear as axioms here.  Six of them are
discharged by proofs in the repository, and the last seven lines audit those proofs:
`Exploding.xfmr_proved` proves the least-action principle of Fey, Meester and Redig,
`Exploding.xlse_lss_bounded_degree` and `Exploding.xlse_lss_general` prove the two
domination theorems of Liggett, Schonmann and Stacey, `Exploding.xmf_proved` proves the hole
bound of Mathieu, `Exploding.xsr_schonmann` proves Schonmann's bootstrap bound, and
`Exploding.xsr_flp` derives the theorem of Fey, Levine and Peres (Theorem 1.1) from it by
`Exploding.LSProof.ls_flp_from_explosive`.  Only the chemical distance of Antal and Pisztora
is assumed.

The default library build includes this module. It can also be built explicitly with
`lake build Exploding.Meta.AxiomsAudit`.
-/

-- Theorems 1.2, 1.3 and 1.4
#print axioms Exploding.limit_shape
#print axioms Exploding.convergence_of_time_constant
#print axioms Exploding.explosive
#print axioms Exploding.explosive_all_high_nonvacuity
-- Section 2
#print axioms Exploding.crossing_time
#print axioms Exploding.renormalization_properties
#print axioms Exploding.local_convexity
-- Section 3
#print axioms Exploding.square_lower_bound
#print axioms Exploding.finite_exploding
#print axioms Exploding.last_wave_bound
#print axioms Exploding.approx_subadditivity
#print axioms Exploding.last_penultimate_cluster
#print axioms Exploding.penultimate_upper_bound
#print axioms Exploding.last_penultimate_close
#print axioms Exploding.convergence_of_the_last_wave
-- Section 4
#print axioms Exploding.approximate_subadditive
-- Section 5
#print axioms Exploding.convergence_of_the_generalized_last_wave
#print axioms Exploding.generalized_convergence
-- Section 6
#print axioms Exploding.counterexample
-- Section 7
#print axioms Exploding.explosion_criteria
#print axioms Exploding.dimensional_reduction
#print axioms Exploding.recurrence
#print axioms Exploding.box_crossing
-- The proofs that discharge six of the cited results
#print axioms Exploding.xfmr_proved
#print axioms Exploding.xlse_lss_bounded_degree
#print axioms Exploding.xlse_lss_general
#print axioms Exploding.xmf_proved
#print axioms Exploding.xsr_schonmann
#print axioms Exploding.xsr_flp
#print axioms Exploding.LSProof.ls_flp_from_explosive

-- Source-space transports, concrete laws, and geometric estimates
#print axioms Exploding.explosion_criteria_v4_premises_nonvacuous
#print axioms Exploding.measurableErgodicOn_iff_omegaErgodicOn
#print axioms Exploding.omegaCoordMeasurableSpace_eq_subtype
#print axioms Exploding.omegaCoord_invariant_iff_exists
#print axioms Exploding.OmegaStationary.map_val_sourceLaw
#print axioms Exploding.OmegaStationary.imageStationaryOn_sourceLaw_iff
#print axioms Exploding.recurrentLaw_map_val_iff
#print axioms Exploding.explosiveLaw_map_subtype_iff
#print axioms Exploding.sourceErgodicOmega_iff_measurableErgodicOn
#print axioms Exploding.sourceErgodicOmega_sourceLaw_iff
#print axioms Exploding.explosive_of_source_ergodic
#print axioms Exploding.arxiv_bond_finite_hole_weighted_tail_summable
#print axioms Exploding.arxiv_actual_bond_core_proximity_ae
#print axioms Exploding.arxiv_bond_finite_hole_translated_box_tail
#print axioms Exploding.arxiv_actual_bond_law_one
#print axioms Exploding.arxiv_actual_bond_reachable_univ_one_ae
#print axioms Exploding.fodo_eq_zero_of_neg
#print axioms Exploding.exists_path_avoiding_site
#print axioms Exploding.pathFillingHyp_nonneg
#print axioms Exploding.bOdo_dimensional_reduction

-- The dimension-one box-crossing case
#print axioms Exploding.bc_dim_one_box_crossing
#print axioms Exploding.bc_dim_one_dirac_one_box_crossing
#print axioms Exploding.bc_box_crossing_all_dims

#print axioms Exploding.source_criterion_vacuity_d2

#print axioms Exploding.waveApproximationHyp_iff_sourceWaveApproximationHyp
#print axioms Exploding.all_high_path_filling_dim_two
#print axioms Exploding.all_high_strongly_box_crossing
#print axioms Exploding.all_high_wave_approximation
#print axioms Exploding.all_high_common_law
#print axioms Exploding.sqw_podo_le_wave_of_stabilized_origin
#print axioms Exploding.sqw_podo_le_wave_of_origin_bound
#print axioms Exploding.squareOrigin_origin_identity
#print axioms Exploding.squareOrigin_odometer_le_green
#print axioms Exploding.podo_eq_sandpile
#print axioms Exploding.pconf_eq_sandpile
#print axioms Exploding.stabilizable_iff_sandpile
#print axioms Exploding.exists_pos_podo_iff_sandpile
#print axioms Exploding.pconf_nonneg
#print axioms Exploding.origin_topples_once_sandpile
#print axioms Exploding.External.FeyDenBoerRedigCubicalCluster
#print axioms Exploding.External.FeyDenBoerRedigCubicalCluster_iff
#print axioms Exploding.External.FeyLevinePeresRadius
#print axioms Exploding.External.FeyLevinePeresRadius_iff
#print axioms Exploding.squareRadiusGreen_terminal_bound

#print axioms Exploding.square_lower_bound_exponential

#print axioms Exploding.square_lower_bound_sharp

#print axioms Exploding.lastWave_bound_complete

#print axioms Exploding.CorrectedSource.renormalization_standing_fields

#print axioms Exploding.CorrectedSource.finite_exploding

#print axioms Exploding.CorrectedSource.last_penultimate_cluster

#print axioms Exploding.CorrectedSource.penultimate_upper_bound

#print axioms Exploding.CorrectedSource.last_penultimate_close

#print axioms Exploding.CorrectedSource.convergence_of_the_last_wave

#print axioms Exploding.CorrectedSource.approximate_subadditive

#print axioms Exploding.squareOrigin_odometer_ge_green

#print axioms Exploding.planar_wave_least_order_exists_unique
#print axioms Exploding.planar_wave_least_order_one

#print axioms Exploding.planar_wave_covering_order_gt_parallel_origin

#print axioms Exploding.planar_wave_cover_order_lower_eventually
#print axioms Exploding.planar_wave_cover_order_upper
#print axioms Exploding.planar_wave_order_bounds
#print axioms Exploding.Frozen.sharp_planar_obstruction
#print axioms Exploding.sharp_planar_obstruction
