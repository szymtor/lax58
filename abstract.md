We define a compositional standard for encoding finitary data as bit strings.
A codec consists of an encoder, a prefix parser, and a structural bit-size
measure. Lawful codecs round-trip their distinguished encodings and have
encoding length equal to the declared size; canonicality, meaning that no
alternative encodings are accepted, is an optional stronger property. We give
standard codecs for primitive data, products, sums, options, lists, finite
indices, vectors, finite functions, multisets, and finite sets. A universal
structural representation supports concise presentations of recursive data,
while a generic `Primcodable` adapter supplies a qualitative fallback. The
interface connects these representations with computability on strings and
lets later formalizations avoid application-specific token grammars.
