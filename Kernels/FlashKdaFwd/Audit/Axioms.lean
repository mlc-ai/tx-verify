-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Proof.CheckForward
import Kernels.FlashKdaFwd.Audit.GateOverflow
import Kernels.FlashKdaFwd.Audit.OutputFormat
import Kernels.FlashKdaFwd.Audit.FiniteTolerance
import Kernels.FlashKdaFwd.Proof.GateAccumulation
import Kernels.FlashKdaFwd.Audit.WarpDot
import Kernels.FlashKdaFwd.Audit.OrthogonalOrder
import Kernels.FlashKdaFwd.Audit.GateSites
import Kernels.FlashKdaFwd.Audit.GateWindow
import Kernels.FlashKdaFwd.Proof.GateRange
import Kernels.FlashKdaFwd.Audit.FiniteMask
import Kernels.FlashKdaFwd.Audit.Tail
import Kernels.FlashKdaFwd.Audit.TailIsolation
import Kernels.FlashKdaFwd.Audit.InputSites
import Kernels.FlashKdaFwd.Audit.NormChoices
import Kernels.FlashKdaFwd.Audit.RootSweep
import Kernels.FlashKdaFwd.Audit.TraceInput
import Kernels.FlashKdaFwd.Audit.InverseSample
import Kernels.FlashKdaFwd.Audit.UpstreamCriteria
import Kernels.FlashKdaFwd.Audit.WeightedSample
import Kernels.FlashKdaFwd.Proof.Seed
import Kernels.FlashKdaFwd.Proof.OperandRound
import Kernels.FlashKdaFwd.Audit.DotOrder
import Kernels.FlashKdaFwd.Audit.OneTokenPipeline
import Kernels.FlashKdaFwd.Audit.Election
import Kernels.FlashKdaFwd.Batches
import Kernels.FlashKdaFwd.Audit.PrefixResult
import Kernels.FlashKdaFwd.Audit.Import
import Kernels.FlashKdaFwd.Audit.PackedNormalize
import Kernels.FlashKdaFwd.Audit.OutputRound
import Kernels.FlashKdaFwd.Audit.Cancellation
import Kernels.FlashKdaFwd.Audit.ResidualSample
import Kernels.FlashKdaFwd.Audit.StatelessCarry
import Kernels.FlashKdaFwd.Audit.StatelessForward
import Kernels.FlashKdaFwd.Audit.Literals

#print axioms FlashKda.Prefix.decode_eq
#print axioms FlashKda.Sequence.forward
#print axioms FlashKda.Block.right_inverse
#print axioms FlashKda.Batches.search_owner
#print axioms FlashKda.FiniteInputs.zero_output
#print axioms FlashKda.FiniteInputs.observed_zero_error
#print axioms FlashKda.FiniteInputs.query_at_most_one
#print axioms FlashKda.Normalize.production_sites
#print axioms FlashKda.Normalize.positive_one_unspecified
#print axioms FlashKda.Election.nonzero_elected
#print axioms FlashKda.Carry.production_reference_difference
#print axioms FlashKda.Carry.flushes_half_minimum
#print axioms FlashKda.Carry.Output.production_state
#print axioms FlashKda.Carry.Output.reference_state
#print axioms FlashKda.Carry.Output.next_tile_views
#print axioms FlashKda.Cancellation.relative_error_one
#print axioms FlashKda.Cancellation.rounds_away_increment
#print axioms FlashKda.Stability.activated_admissible
#print axioms FlashKda.Stability.accumulated
#print axioms FlashKda.Stability.output_bound
#print axioms FlashKda.Literals.source_literals
#print axioms FlashKda.Literals.forward
#print axioms FlashKda.Literals.unit_normalization
#print axioms FlashKda.Stateless.exact_output_rounds_up
#print axioms FlashKda.Stateless.measured_output_differs
#print axioms FlashKda.Stateless.second_tile
#print axioms FlashKda.Prefix.word_increment
#print axioms FlashKda.Prefix.idle_lanes
#print axioms FlashKda.Prefix.final_of_replay
#print axioms FlashKda.Prefix.packed_final_memory

#print axioms FlashKda.Normalize.production_reduction
#print axioms FlashKda.Normalize.row_coverage
#print axioms FlashKda.OneToken.real_answer
#print axioms FlashKda.OneToken.workspace_words
#print axioms FlashKda.OneToken.workspace_dot
#print axioms FlashKda.OneToken.rounded_dot
#print axioms FlashKda.OneToken.rounded_output
#print axioms FlashKda.OneToken.no_relative_bound
#print axioms FlashKda.OneToken.sevenfold_error
#print axioms FlashKda.OneToken.squared_norm_inputs
#print axioms FlashKda.OneToken.normalized_values
#print axioms FlashKda.Normalize.production_normalize
#print axioms FlashKda.Normalize.thread_offsets
#print axioms FlashKda.OneToken.positive_rounded_forward

#print axioms FlashKda.Normalize.implicit_add_unspecified
#print axioms FlashKda.Normalize.checked_sums
#print axioms FlashKda.Binary.binary_routes
#print axioms FlashKda.Binary.binary_arguments
#print axioms FlashKda.Binary.all_root_words
#print axioms FlashKda.Binary.observed_roots
#print axioms FlashKda.Binary.all_rounded_outputs
#print axioms FlashKda.Binary.Dot.tree_exact
#print axioms FlashKda.Binary.Dot.full_cell

#print axioms FlashKda.Residual.defect
#print axioms FlashKda.Residual.outputs
#print axioms FlashKda.Residual.final_state
#print axioms FlashKda.Sample.initial_words
#print axioms FlashKda.Sample.packed_words
#print axioms FlashKda.Sample.packed_outputs
#print axioms FlashKda.Sample.checked
#print axioms FlashKda.Sample.outputs
#print axioms FlashKda.Sample.final_state
#print axioms FlashKda.Sample.zero_channels

#print axioms FlashKda.Import.target
#print axioms FlashKda.Import.total
#print axioms FlashKda.Normalize.same_lanes

#print axioms FlashKda.Criteria.words
#print axioms FlashKda.Criteria.upstream_incompatible
#print axioms FlashKda.Criteria.measured_rejected
#print axioms FlashKda.Criteria.real_rejected
#print axioms FlashKda.InverseStability.column_energy
#print axioms FlashKda.InverseStability.solve_error
#print axioms FlashKda.InverseStability.inverse_residual
#print axioms FlashKda.InverseStability.correction_error
#print axioms FlashKda.Seed.converted_entry
#print axioms FlashKda.Seed.entry
#print axioms FlashKda.Seed.seed_budget
#print axioms FlashKda.Seed.perturb
#print axioms FlashKda.Seed.perturbed_inverse_norm
#print axioms FlashKda.OperandRound.relative
#print axioms FlashKda.Sample.InverseCheck.finite_words
#print axioms FlashKda.Sample.InverseCheck.bounded

#print axioms FlashKda.Stateless.Trace.decoded
#print axioms FlashKda.Stateless.Trace.converted_update
#print axioms FlashKda.Stateless.Trace.store
#print axioms FlashKda.Stateless.Trace.bytes
#print axioms FlashKda.Stateless.Reconstruction.support
#print axioms FlashKda.Stateless.Reconstruction.discrepancy
#print axioms FlashKda.Stateless.Reconstruction.carry_trace
#print axioms FlashKda.Stateless.Reconstruction.publication

#print axioms FlashKda.Stateless.RawTrace.public_disagrees
#print axioms FlashKda.Stateless.RawTrace.absolute_error

#print axioms FlashKda.ValuePerturbation.states
#print axioms FlashKda.ValuePerturbation.forward
#print axioms FlashKda.ValuePerturbation.positive_strength
#print axioms FlashKda.Sample.Weighted.finite
#print axioms FlashKda.Sample.Weighted.bounds

#print axioms FlashKda.RootContract.exists_allowed
#print axioms FlashKda.RootContract.normal_result
#print axioms FlashKda.RootExecution.outcomes
#print axioms FlashKda.RootExecution.special
#print axioms FlashKda.NormChoices.decoded
#print axioms FlashKda.NormChoices.successors
#print axioms FlashKda.NormChoices.arithmetic_result
#print axioms FlashKda.NormChoices.from_execution
#print axioms FlashKda.RootSweep.covers
#print axioms FlashKda.RootSweep.squared_integer
#print axioms FlashKda.RootSweep.shifted_limbs
#print axioms FlashKda.RootSweep.attained
#print axioms FlashKda.RootSweep.within
#print axioms FlashKda.RootSweep.tight

#print axioms FlashKda.InputTile.byte_count
#print axioms FlashKda.InputTile.shared
#print axioms FlashKda.InputTile.global
#print axioms FlashKda.InputTile.completed
#print axioms FlashKda.InputTile.decoded
#print axioms FlashKda.InputTile.packed_offset

#print axioms FlashKda.Tail.decoded
#print axioms FlashKda.Tail.all_writers
#print axioms FlashKda.Tail.touches_iff
#print axioms FlashKda.NormRange.root_argument
#print axioms FlashKda.FiniteMask.widened_bits
#print axioms FlashKda.FiniteMask.widen_register
#print axioms FlashKda.FiniteMask.same_sum
#print axioms FlashKda.FiniteMask.finite_mask
#print axioms FlashKda.TailIsolation.single_difference
#print axioms FlashKda.TailIsolation.first_rounded
#print axioms FlashKda.TailIsolation.reduction
#print axioms FlashKda.TailIsolation.cleared_key
#print axioms FlashKda.TailIsolation.observed_words
#print axioms FlashKda.TailIsolation.no_isolated_result

#print axioms FlashKda.GateSites.decoded
#print axioms FlashKda.GatePair.attainable
#print axioms FlashKda.GateRange.bounded_prefix
#print axioms FlashKda.GateRange.paired_prefix
#print axioms FlashKda.GateRange.ordered
#print axioms FlashKda.GatePair.product
#print axioms FlashKda.GatedOperands.score
#print axioms FlashKda.GatedOperands.from_prefixes
#print axioms FlashKda.Orthogonal.real_output
#print axioms FlashKda.Orthogonal.first_state
#print axioms FlashKda.Orthogonal.exponential_range
#print axioms FlashKda.Orthogonal.unique_operands
#print axioms FlashKda.Orthogonal.stored_matches
#print axioms FlashKda.Orthogonal.contraction
#print axioms FlashKda.Orthogonal.conversions
#print axioms FlashKda.Orthogonal.readout_in_any_order
#print axioms FlashKda.Orthogonal.readout_forced
#print axioms FlashKda.Orthogonal.observed_error

#print axioms FlashKda.FiniteInputs.no_finite_tolerance
#print axioms FlashKda.WarpDot.fragment_locations
#print axioms FlashKda.WarpDot.decoded
#print axioms FlashKda.GateAccumulation.from_prefixes

#print axioms FlashKda.Enclosure.measured_forward
#print axioms FlashKda.Enclosure.max_step
#print axioms FlashKda.Enclosure.scan_ok
#print axioms FlashKda.Enclosure.word_ok

#print axioms FlashKda.GateOverflow.decoded
#print axioms FlashKda.GateOverflow.store_decoded
#print axioms FlashKda.GateOverflow.firstGate_inf
#print axioms FlashKda.GateOverflow.argument_100
#print axioms FlashKda.GateOverflow.threshold
#print axioms FlashKda.GateOverflow.nan_prefix
#print axioms FlashKda.GateOverflow.real_gate
#print axioms FlashKda.FiniteInputs.zero_state_at
#print axioms FlashKda.FiniteInputs.zero_output_at

#print axioms FlashKda.OutputFormat.near_zero
#print axioms FlashKda.OutputFormat.above_range
#print axioms FlashKda.OutputFormat.correctly_rounded
#print axioms FlashKda.OutputFormat.optimal_relative
#print axioms FlashKda.OutputFormat.large_impossible
#print axioms FlashKda.OutputFormat.large_rms
#print axioms FlashKda.OutputFormat.captured_scale
