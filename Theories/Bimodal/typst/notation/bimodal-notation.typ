// ============================================================================
// bimodal-notation.typ
// Notation module for Bimodal TM logic documentation
//
// Provides notation for the bimodal logic combining S5 modality and
// linear temporal operators.
//
// Imports shared notation from shared-notation.typ
// ============================================================================

#import "shared-notation.typ": *

// ============================================================================
// Formula Syntax (Bimodal-specific)
// ============================================================================

// --- Temporal Operators ---
#let allpast = $H$
#let allfuture = $G$
#let somepast = $P$
#let somefuture = $F$

// --- Combined Temporal (always/sometimes triangles) ---
// Using filled triangles for visual distinction
#let always = $triangle.stroked.t$
#let sometimes = $triangle.stroked.b$

// --- Temporal Swap Operation ---
#let swap = $chevron.l S chevron.r$

// ============================================================================
// Semantics (Bimodal-specific)
// ============================================================================

// --- Frame Structure ---
#let taskframe = $cal(F)$
#let Dur = $cal(D)$
#let worldstate = $W$
#let taskrel = $R$

// Task relation arrow: w => x => u means w transitions to u with duration x
#let taskto(x) = $arrow.r.double.long_#x$

// --- Model Structure ---
// model is imported from shared-notation.typ
#let valuation = $V$

// --- World History ---
#let history = $tau$
#let althistory = $sigma$
#let domain = $"dom"$
#let histories = $H$

// --- Truth Relation ---
#let satisfies = $tack.r.double$
#let notsatisfies = $tack.r.double.not$
#let truthat(m, t, x, phi) = $#m, #t, #x #satisfies #phi$

// ============================================================================
// Proof Theory (Bimodal-specific extensions)
// ============================================================================

// --- Derivability ---
// proves and ctx are imported from shared-notation.typ
#let derivable(gamma, phi) = $#gamma #proves #phi$

// --- Validity ---
#let valid(phi) = $#proves #phi$
#let framevalid(f, phi) = $#f #satisfies #phi$

// ============================================================================
// Metalanguage Connectives
// ============================================================================

// Metalanguage biconditional (distinct from object language iff)
#let Iff = [~_iff_~]

// ============================================================================
// Lean Identifier Commands
// ============================================================================

#let leanTaskRel = raw("task_rel")
#let leanTimeShift = raw("time_shift")
#let leanRespTask = raw("respects_task")
#let leanConvex = raw("convex")
#let leanDomain = raw("domain")
#let leanStates = raw("states")
#let leanNullity = raw("nullity")
#let leanCompositionality = raw("compositionality")
