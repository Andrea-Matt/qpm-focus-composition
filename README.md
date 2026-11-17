# Question–partition matching in focus composition

This repository contains the poster I presented at the Fall School "Alternatives in grammar" in Göttingen on November 18, 2026: [`poster.pdf`](poster.pdf).

The poster comes with a project that contains the formalization in Lean 4 behind it: the definitions of the system and proofs of its claims.

## The Lean formalization

- The project is organized in two parts. The main part holds the definitions and results, and it can be read by a semanticist who reads Lean code. A separate collection of lemmas is used only inside proofs, and never in definitions and theorem statements: that need not be read and is kept aside so that the main part is less crowded.
- There is no `sorry`. A check run at every build guarantees that the lemmas occur in no definition or theorem statement, and that every definition and result of the main part uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The proofs were developed with the help of Claude Code (Anthropic).

## Files

- [`Composition.lean`](Composition.lean): the list of the cases, each sentence with its translation in the logical language.
- The main part, in `Composition/`:
  - [`Questions.lean`](Composition/Questions.lean): exhaustification and question–partition matching;
  - [`Apparatus.lean`](Composition/Apparatus.lean): truth values, fuzzy logic, the modal operators, assertion;
  - [`Ontology.lean`](Composition/Ontology.lean): pluralities, focus, focus on sets;
  - [`Lexicon.lean`](Composition/Lexicon.lean): the lexical items, and the alternatives of coordinations;
  - [`Examples/NonModal.lean`](Composition/Examples/NonModal.lean) and [`Examples/Modal.lean`](Composition/Examples/Modal.lean): the predictions, each case stated by the exact contexts it matches and illustrated in a model with three drinks;
  - [`Examples/Drinks.lean`](Composition/Examples/Drinks.lean): that model.
- [`Composition/Lemmas/`](Composition/Lemmas): the lemmas used only inside proofs.
- [`Composition/Audit.lean`](Composition/Audit.lean): the check run at every build.

## Building

Install Lean with [elan](https://github.com/leanprover/elan), Lean's version manager; it reads the version to use from `lean-toolchain`. Then, in this folder:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib already compiled (several GB), the second builds the project and runs the check.

## License

MIT; see [`LICENSE`](LICENSE).
