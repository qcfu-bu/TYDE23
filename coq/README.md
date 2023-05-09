# Coq formalization of CILC

## Dependencies
- `coq-mathcomp-ssreflect`
- `coq-autosubst`

Tested on Coq 8.17.0

## Usage

Once dependencies have been met, run `make` in the `theories` directory.

## Organization

- `clc_context.v`      : Formalization of CILC contexts and lemmas for manipulating them.
- `clc_ast.v`          : AST of raw CILC terms and single step reduction.
- `clc_confluence.v`   : Confluence and injectivity lemmas for conversion.
- `clc_subtype.v`      : Formalization of subtyping relation.
- `clc_typing.v`       : Formalization of the CILC type system.
- `clc_weakening.v`    : Proof of weakening lemmas.
- `clc_substitution.v` : Proof of substitution lemmas.
- `clc_inversion.v`    : Proof of various inversion lemmas.
- `clc_arity_spine.v`  : Various lemmas for manipulating arities and spine forms.
- `clc_validity.v`     : Proof of type validity theorem.
- `clc_typing_spine.v` : Formalization of a "typing spine" structure.
- `clc_respine.v`      : Lemmas for "unapplying" and "reapplying" typing spines.
- `clc_iota_lemma.v`   : Lemmas for proving the soundness of ι-reductions.
- `clc_soundness.v`    : Type soundness theorem of CILC.
- `clc_resolution.v`   : Proof of pointer resolution theorem.
- `clc_resolve_spine.v`: Resolve pointers in spine form.
- `clc_semantics.v`    : Heap semantics soundness for CILC.

### Definitions

The following table shows the file containing the encodings of various judgments.

| name in paper            | file                                            |
|--------------------------|-------------------------------------------------|
| Syntax of CILC           | [clc_ast.v](./theories/clc_ast.v)               |
| Standard Reduction       | [clc_ast.v](./theories/clc_ast.v)               |
| Sort Order               | [clc_context.v](./theories/clc_context.v)       |
| Context                  | [clc_context.v](./theories/clc_context.v)       |
| Context Merge            | [clc_context.v](./theories/clc_context.v)       |
| Context Constraint       | [clc_context.v](./theories/clc_context.v)       |
| Context Restriction      | [clc_context.v](./theories/clc_context.v)       |
| Core Typing Rules        | [clc_typing.v](./theories/clc_typing.v)         |
| Subtyping                | [clc_subtype.v](./theories/clc_subtype.v)       |
| Arities                  | [clc_typing.v](./theories/clc_typing.v)         |
| Well-formed Constructors | [clc_typing.v](./theories/clc_typing.v)         |
| Motive Types             | [clc_typing.v](./theories/clc_typing.v)         |
| Branch Types             | [clc_typing.v](./theories/clc_typing.v)         |
| Conditional Apply        | [clc_typing.v](./theories/clc_typing.v)         |
| Inductive Scheme         | [clc_typing.v](./theories/clc_typing.v)         |
| Lookup                   | [clc_resolution.v](./theories/clc_resolution.v) |
| Values                   | [clc_resolution.v](./theories/clc_resolution.v) |
| Heap Reduction           | [clc_semantics.v](./theories/clc_semantics.v)   |
| Resolve                  | [clc_resolution.v](./theories/clc_resolution.v) |
| Well-Resolved            | [clc_resolution.v](./theories/clc_resolution.v) |
| WR-Heaps                 | [clc_resolution.v](./theories/clc_resolution.v) |

### Meta Theory

Meta theorems presented in the paper can be found in the following files.
We did not formalize the theorems concerning strong normalization theorems described in Section 6.5.

| name in paper                 | file                                                |
|-------------------------------|-----------------------------------------------------|
| Theorem 1 (Confluence)        | [clc_confluence.v](./theories/clc_confluence.v)     |
| Theorem 2 (Weakening)         | [clc_weakening.v](./theories/clc_weakening.v)       |
| Theorem 3 (Substitution)      | [clc_substitution.v](./theories/clc_substitution.v) |
| Theorem 4 (Validity)          | [clc_validity](./theories/clc_validity.v)           |
| Theorem 5 (Subject Reduction) | [clc_soundness.v](./theories/clc_soundness.v)       |
| Theorem 8 (Resolution)        | [clc_resolution.v](./theories/clc_resolution.v)     |
| Theorem 9 (Heap-Soundness)    | [clc_semantics.v](./theories/clc_semantics.v)       |
    
