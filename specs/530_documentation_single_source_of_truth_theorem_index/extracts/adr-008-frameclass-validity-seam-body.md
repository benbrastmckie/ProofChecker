The seam has two acceptable resolutions and two rejected relocations. This ADR records the
rejected ones, so that the rationale does not have to live in a module docstring.

### Rejected: relocate `inductive FrameClass` into a shared low-level module

This would remove the `Semantics -> ProofSystem` import edge entirely. It would also move a
namespace carrying 45 axiom constructors, along with every `DerivationTree` / `Derivable`
signature that names them, into a module below both layers. The edge it removes is a single
import of `ProofSystem/Axioms.lean`, which itself imports only `Syntax/Formula.lean`; the churn
it creates touches the whole proof side. Rejected on cost.

### Rejected: relocate the four class-restricted validity predicates

`ValidIn` is defined through `TaskFrame.ValidOn` (`def:frame-validity`), declared in
`Semantics/Validity.lean`, and `Validity.lean`'s own class-restricted predicates (`ValidDense`,
`ValidZTime`, `ValidComplete`, `ValidRTime`) are instances of `ValidIn` / `ValidOnFrames`. Those
two facts cannot both hold with `ValidIn` downstream of `Validity.lean`. Moving the four
predicates into `FrameClassValidity.lean` and re-exporting them would have forced a new import
line into each of the roughly 27 files that consume them today, for no gain in layering.
Rejected on cost.
