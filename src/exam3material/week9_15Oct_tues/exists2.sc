// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// !(∃ x (P(x) & Q(x))) ⊢ ∀ x (P(x) __>: ¬Q(x))

@pure def exists1[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    //@formatter: off

    (
      !(∃((x: T) => (P(x) & Q(x))))
    )
    |-
    (
      ∀((x: T) => (P(x)) __>: !Q(x))
    )
      Proof(
      1 ( !(∃((x: T) => (P(x) & Q(x)))) ) by Premise,
      2 Let((a: T) =>SubProof(
        3 SubProof(
          4 Assume(P(a)),
          5 SubProof(
            6 Assume(Q(a)),
            7 (P(a) & Q(a)) by AndI(4, 6),
            8 ((∃((x: T) => (P(x) & Q(x))))) by ExistsI[T](7),
            9 (F) by NegE(8, 1),
          ),
          10 (!Q(a)) by NegI(5),
        ),
        11 (P(a) __>: !Q(a)) by ImplyI(3),
      )),
      12 (∀((x: T) => (P(x)) __>: !Q(x))) by AllI[T](2)
    )
    //@formatter:on
  )
}