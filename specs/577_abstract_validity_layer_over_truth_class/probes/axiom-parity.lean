/-
AXIOM-PARITY PROBE -- the pre/post refactor axiom-set gate for the abstract validity layer.

Run: `lake env lean specs/.../probes/axiom-parity.lean 2>/dev/null`
and diff the output against `04_axiom-baseline.txt`. The baseline was captured BEFORE any
proof body was replaced by a delegation to the generic layer, so a non-empty diff means a
generic proof reached for a tactic (`by_contra`, `push_neg`, a classical `simp` lemma) that
the original did not. That is a defect to fix in the GENERIC proof, never a rebaseline.

Covers every category-A theorem and every category-B clause lemma of
`04_scope-enumeration.txt` -- the complete set of names whose bodies this refactor replaces.
-/
import FormalSystem.Semantics.StarValidity
import FormalSystem.Semantics.MinusValidity
import FormalSystem.Semantics.PlusValidity

#print axioms FormalSystem.Semantics.MinusTruth.always_iff
#print axioms FormalSystem.Semantics.MinusTruth.and_iff
#print axioms FormalSystem.Semantics.MinusTruth.diamond_iff
#print axioms FormalSystem.Semantics.MinusTruth.neg_iff
#print axioms FormalSystem.Semantics.MinusTruth.or_iff
#print axioms FormalSystem.Semantics.MinusTruth.someFuture_iff
#print axioms FormalSystem.Semantics.MinusTruth.somePast_iff
#print axioms FormalSystem.Semantics.MinusTruth.top_true
#print axioms FormalSystem.Semantics.MinusValid.apply
#print axioms FormalSystem.Semantics.MinusValid.of_forall_total
#print axioms FormalSystem.Semantics.MinusValidIn.apply_total
#print axioms FormalSystem.Semantics.MinusValidIn.mono
#print axioms FormalSystem.Semantics.MinusValidIn.of_forall_total
#print axioms FormalSystem.Semantics.MinusValidOnFrames.apply_total
#print axioms FormalSystem.Semantics.MinusValidOnFrames.mono
#print axioms FormalSystem.Semantics.MinusValidOnFrames.of_forall_total
#print axioms FormalSystem.Semantics.PlusTruth.allFuture_iff
#print axioms FormalSystem.Semantics.PlusTruth.allPast_iff
#print axioms FormalSystem.Semantics.PlusTruth.and_iff
#print axioms FormalSystem.Semantics.PlusTruth.diamond_iff
#print axioms FormalSystem.Semantics.PlusTruth.dstab_iff
#print axioms FormalSystem.Semantics.PlusTruth.neg_iff
#print axioms FormalSystem.Semantics.PlusTruth.or_iff
#print axioms FormalSystem.Semantics.PlusTruth.someFuture_iff
#print axioms FormalSystem.Semantics.PlusTruth.somePast_iff
#print axioms FormalSystem.Semantics.PlusTruth.top_true
#print axioms FormalSystem.Semantics.PlusValid.apply
#print axioms FormalSystem.Semantics.PlusValid.of_forall_total
#print axioms FormalSystem.Semantics.PlusValidIn.apply_total
#print axioms FormalSystem.Semantics.PlusValidIn.mono
#print axioms FormalSystem.Semantics.PlusValidIn.of_forall_total
#print axioms FormalSystem.Semantics.PlusValidOnFrames.apply_total
#print axioms FormalSystem.Semantics.PlusValidOnFrames.mono
#print axioms FormalSystem.Semantics.PlusValidOnFrames.of_forall_total
#print axioms FormalSystem.Semantics.StarTruth.allFuture_iff
#print axioms FormalSystem.Semantics.StarTruth.allPast_iff
#print axioms FormalSystem.Semantics.StarTruth.always_iff
#print axioms FormalSystem.Semantics.StarTruth.and_iff
#print axioms FormalSystem.Semantics.StarTruth.diamond_iff
#print axioms FormalSystem.Semantics.StarTruth.dstab_iff
#print axioms FormalSystem.Semantics.StarTruth.neg_iff
#print axioms FormalSystem.Semantics.StarTruth.or_iff
#print axioms FormalSystem.Semantics.StarTruth.someFuture_iff
#print axioms FormalSystem.Semantics.StarTruth.somePast_iff
#print axioms FormalSystem.Semantics.StarTruth.top_true
#print axioms FormalSystem.Semantics.StarValid.apply
#print axioms FormalSystem.Semantics.StarValid.of_forall_total
#print axioms FormalSystem.Semantics.StarValidIn.apply_total
#print axioms FormalSystem.Semantics.StarValidIn.mono
#print axioms FormalSystem.Semantics.StarValidIn.of_forall_total
#print axioms FormalSystem.Semantics.StarValidOnFrames.apply_total
#print axioms FormalSystem.Semantics.StarValidOnFrames.mono
#print axioms FormalSystem.Semantics.StarValidOnFrames.of_forall_total
#print axioms FormalSystem.Semantics.TaskFrame.StarValidOn.apply_total
#print axioms FormalSystem.Semantics.TaskFrame.StarValidOn.of_forall_total
#print axioms FormalSystem.Semantics.TaskFrame.validOn_iff_total
#print axioms FormalSystem.Semantics.Truth.always_iff_tri
#print axioms FormalSystem.Semantics.Truth.and_iff
#print axioms FormalSystem.Semantics.Truth.diamond_iff
#print axioms FormalSystem.Semantics.Truth.future_iff
#print axioms FormalSystem.Semantics.Truth.neg_iff
#print axioms FormalSystem.Semantics.Truth.or_iff
#print axioms FormalSystem.Semantics.Truth.past_iff
#print axioms FormalSystem.Semantics.Truth.some_future_iff
#print axioms FormalSystem.Semantics.Truth.some_past_iff
#print axioms FormalSystem.Semantics.Truth.top_true
#print axioms FormalSystem.Semantics.Valid.apply
#print axioms FormalSystem.Semantics.Valid.of_forall_total
#print axioms FormalSystem.Semantics.Valid.of_not
#print axioms FormalSystem.Semantics.ValidIn.apply_total
#print axioms FormalSystem.Semantics.ValidIn.mono
#print axioms FormalSystem.Semantics.ValidIn.of_forall_total
#print axioms FormalSystem.Semantics.ValidIn.of_not
#print axioms FormalSystem.Semantics.ValidOnFrames.apply_total
#print axioms FormalSystem.Semantics.ValidOnFrames.mono
#print axioms FormalSystem.Semantics.ValidOnFrames.of_forall_total
#print axioms FormalSystem.Semantics.ValidOnFrames.of_not
