import Composition.Apparatus
import Composition.Questions
import Composition.Ontology
import Composition.Lexicon
import Composition.Examples.Drinks
import Composition.Examples.NonModal
import Composition.Examples.Modal
import Composition.Audit

/-!
# Composition

Root of the `Composition` library: the machinery of focus and coordination, and its predictions.
`Audit` comes last and checks the readable/auxiliary separation.

## The cases in `Examples/`

`pred` is the predicate *drink*, `⋆pred` its plural, `Foc A a ha` the focused item `[a]_F` with
alternatives `A`, and `acc` the accessibility relation of the modals.

Without modals (`Examples/NonModal.lean`):

* *Taro drank [a]_F*
  ```
  ⋆pred <$> Foc A a ha
  ```
* *Taro drank [a]_F and [b]_F*
  ```
  ⋆pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb)
  ```
* *Taro didn't drink [a]_F*
  ```
  NL.not <$> (⋆pred <$> Foc A a ha)
  ```
* *Taro didn't drink [a]_F and [b]_F*
  ```
  NL.not <$> (⋆pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb))
  ```
* *Taro didn't drink both [a]_F and [b]_F*
  ```
  NL.not <$> (NL.both pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb))
  ```
* *Taro drank [a]_F or [b]_F*
  ```
  (⋆pred <$> ·) <$> NL.or {Foc A a ha} {Foc A b hb}
  ```

With modals (`Examples/Modal.lean`):

* *Taro can drink [a]_F or [b]_F*
  ```
  NL.can acc <$> ((⋆pred <$> ·) <$>
    (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))
  ```
* *Taro must drink [a]_F or [b]_F*
  ```
  NL.must acc <$> ((⋆pred <$> ·) <$>
    (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))
  ```
* *Taro can't drink both [a]_F and [b]_F*
  ```
  NL.not <$> (NL.can acc <$> ((NL.both pred <$> ·) <$>
    (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))
  ```
* *Taro doesn't have to drink both [a]_F and [b]_F*
  ```
  NL.not <$> (NL.must acc <$> ((NL.both pred <$> ·) <$>
    (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))
  ```

The illustrations use the three-drink model of `Examples/Drinks.lean`.
-/
