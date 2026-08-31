We define a canonical, compositional standard for encoding finitary data as
bit strings. A codec consists of an encoder, a prefix parser, and a structural
bit-size measure. Lawful codecs parse an encoded value from the front of any
suffix, accept only canonical encodings, and have encoding length equal to the
declared size. We give standard codecs for natural numbers and the usual
finitary type constructors, including products, sums, options, lists, finite
indices, vectors, finite functions, and finite sets. We also connect these
codecs with computability on strings. The resulting interface lets later
formalizations state effective constructions over readable structured objects
without exposing application-specific token grammars.
