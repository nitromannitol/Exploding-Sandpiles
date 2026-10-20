#!/usr/bin/env python3
"""Require one exact standard-axiom report for each theorem printed by
Exploding/Meta/AxiomsAudit.lean.

    lake build Exploding.Meta.AxiomsAudit 2>&1 | tee axioms-audit.log
    python3 scripts/check_axioms.py axioms-audit.log

Lean may wrap a long report over several lines; each report is joined before it is read.
"""
import pathlib
import re
import sys

expected = {
    'Exploding.fey_levine_peres_explosive',
    'Exploding.limit_shape',
    'Exploding.convergence_of_time_constant',
    'Exploding.explosive',
    'Exploding.explosive_all_high_nonvacuity',
    'Exploding.crossing_time',
    'Exploding.renormalization_properties',
    'Exploding.local_convexity',
    'Exploding.square_lower_bound',
    'Exploding.finite_exploding',
    'Exploding.last_wave_bound',
    'Exploding.approx_subadditivity',
    'Exploding.last_penultimate_cluster',
    'Exploding.penultimate_upper_bound',
    'Exploding.last_penultimate_close',
    'Exploding.convergence_of_the_last_wave',
    'Exploding.approximate_subadditive',
    'Exploding.convergence_of_the_generalized_last_wave',
    'Exploding.generalized_convergence',
    'Exploding.counterexample',
    'Exploding.explosion_criteria',
    'Exploding.dimensional_reduction',
    'Exploding.recurrence',
    'Exploding.schonmann_bootstrap',
    'Exploding.box_crossing',
    'Exploding.xfmr_proved',
    'Exploding.xlse_lss_bounded_degree',
    'Exploding.xlse_lss_general',
    'Exploding.xmf_proved',
    'Exploding.xsr_schonmann',
    'Exploding.xsr_flp',
    'Exploding.LSProof.ls_flp_from_explosive',
    'Exploding.explosion_criteria_premises_nonvacuous',
    'Exploding.measurableErgodicOn_iff_omegaErgodicOn',
    'Exploding.omegaCoordMeasurableSpace_eq_subtype',
    'Exploding.omegaCoord_invariant_iff_exists',
    'Exploding.OmegaStationary.map_val_sourceLaw',
    'Exploding.OmegaStationary.imageStationaryOn_sourceLaw_iff',
    'Exploding.recurrentLaw_map_val_iff',
    'Exploding.explosiveLaw_map_subtype_iff',
    'Exploding.sourceErgodicOmega_iff_measurableErgodicOn',
    'Exploding.sourceErgodicOmega_sourceLaw_iff',
    'Exploding.explosive_of_source_ergodic',
    'Exploding.arxiv_bond_finite_hole_weighted_tail_summable',
    'Exploding.arxiv_actual_bond_core_proximity_ae',
    'Exploding.arxiv_bond_finite_hole_translated_box_tail',
    'Exploding.arxiv_actual_bond_law_one',
    'Exploding.arxiv_actual_bond_reachable_univ_one_ae',
    'Exploding.fodo_eq_zero_of_neg',
    'Exploding.exists_path_avoiding_site',
    'Exploding.pathFillingHyp_nonneg',
    'Exploding.bOdo_dimensional_reduction',
    'Exploding.bc_dim_one_box_crossing',
    'Exploding.bc_dim_one_dirac_one_box_crossing',
    'Exploding.bc_box_crossing_all_dims',
    'Exploding.source_criterion_vacuity_d2',
    'Exploding.waveApproximationHyp_iff_sourceWaveApproximationHyp',
    'Exploding.all_high_path_filling_dim_two',
    'Exploding.all_high_strongly_box_crossing',
    'Exploding.all_high_wave_approximation',
    'Exploding.all_high_common_law',
    'Exploding.sqw_podo_le_wave_of_stabilized_origin',
    'Exploding.sqw_podo_le_wave_of_origin_bound',
    'Exploding.squareOrigin_origin_identity',
    'Exploding.squareOrigin_odometer_le_green',
    'Exploding.podo_eq_sandpile',
    'Exploding.pconf_eq_sandpile',
    'Exploding.stabilizable_iff_sandpile',
    'Exploding.exists_pos_podo_iff_sandpile',
    'Exploding.pconf_nonneg',
    'Exploding.origin_topples_once_sandpile',
    'Exploding.External.FeyDenBoerRedigCubicalCluster',
    'Exploding.External.FeyDenBoerRedigCubicalCluster_iff',
    'Exploding.External.FeyLevinePeresRadius',
    'Exploding.External.FeyLevinePeresRadius_iff',
    'Exploding.squareRadiusGreen_terminal_bound',
    'Exploding.square_lower_bound_exponential',
    'Exploding.square_lower_bound_sharp',
    'Exploding.lastWave_bound_complete',
    'Exploding.CorrectedSource.renormalization_standing_fields',
    'Exploding.CorrectedSource.finite_exploding',
    'Exploding.CorrectedSource.last_penultimate_cluster',
    'Exploding.CorrectedSource.penultimate_upper_bound',
    'Exploding.CorrectedSource.last_penultimate_close',
    'Exploding.CorrectedSource.convergence_of_the_last_wave',
    'Exploding.CorrectedSource.approximate_subadditive',
    'Exploding.squareOrigin_odometer_ge_green',
    'Exploding.planar_wave_least_order_exists_unique',
    'Exploding.planar_wave_least_order_one',
    'Exploding.planar_wave_covering_order_gt_parallel_origin',
    'Exploding.planar_wave_cover_order_lower_eventually',
    'Exploding.planar_wave_cover_order_upper',
    'Exploding.planar_wave_order_bounds',
    'Exploding.Frozen.sharp_planar_obstruction',
    'Exploding.sharp_planar_obstruction',
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
log = pathlib.Path(sys.argv[1]).read_text(encoding='utf-8', errors='replace')
if re.search(r'warning:|sorryAx|declaration uses .sorry', log, re.IGNORECASE):
    raise SystemExit('Axiom audit emitted a warning or reported sorryAx')
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
if log.count('depends on axioms') != len(reports):
    raise SystemExit('An axiom report could not be read')
seen = set()
for theorem, axioms in reports:
    if theorem not in expected or theorem in seen:
        raise SystemExit('Unexpected or duplicate axiom report: ' + theorem)
    actual = [a.strip() for a in axioms.split(',')]
    if len(actual) != 3 or set(actual) != standard:
        raise SystemExit('Unexpected axioms for ' + theorem + ': ' + ' '.join(axioms.split()))
    seen.add(theorem)
if seen != expected:
    raise SystemExit('Missing axiom reports: ' + ', '.join(sorted(expected - seen)))
print('All %d results use exactly propext, Classical.choice and Quot.sound.' % len(expected))
