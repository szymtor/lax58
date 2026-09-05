We define a neutral structural input convention for finite constructor data.
Values are represented by binary trees with natural-number leaves; structural
size counts tree nodes while primitive payload magnitude is tracked
separately. A small fixed vocabulary constructs natural-number, product, and
ordered-list presentations required by the current downstream application.
A closed derivation command generates datatype encoders, complete constructor
equations, and checked witnesses together. It accepts only natural numbers,
finite indices, proof-erased subtypes, finite families, and previously derived
datatypes. Unsupported fields fail elaboration; arbitrary field encoders have
no access to this certified path. The generated equations remain inspectable
and kernel-checked.

The mathematical concepts are structural presentations, their fixed
combinators, and the distinguished word arena. Separate, explicitly labeled
infrastructure modules provide encoding-agreement bookkeeping and derivation
tools; an arbitrary agreement value is not itself a provenance certificate.

Every structural value has a distinguished dense immutable word arena. The
arena stores exactly three words per structural node plus one root word,
faithfully represents its source, and supplies the distinguished Lax word-RAM
input tape consisting of that root followed by the arena. It fits in fixed-width
word memory under separate payload and address-space hypotheses. The submission does not
provide binary serialization, mutable-heap semantics, operation costs, or an
algorithmic runtime model.
