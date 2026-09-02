We define a neutral structural input convention for finite constructor data.
Values are represented by binary trees with natural-number leaves; structural
size counts tree nodes while primitive payload magnitude is tracked
separately. A small fixed vocabulary constructs presentations for the ordinary
type formers needed by downstream applications. Datatype-specific
structurality is certified by complete constructor equations, preventing a
representation from attaching derived advice or hidden preprocessing.

Every structural value has a distinguished dense immutable word arena. The
arena stores exactly three words per structural node plus one supplied root
address, faithfully represents its source, and fits in fixed-width word memory
under separate payload and address-space hypotheses. The submission does not
provide binary serialization, mutable-heap semantics, operation costs, or an
algorithmic runtime model.
