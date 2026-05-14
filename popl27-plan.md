## Plan

### §1.1

- Currently we say "the forward analysis tells whether it's sufficient to compute the output". I think we can
  present that as one kind of forward analysis but also introduce the other intuition too: an alternative
  forward map can tell us whether an input is _necessary_ to compute some part of the output.

- New section here introducing the "Bool Jacobean" idea: that we can understand these I/O dependencies in
  terms of a matrix where each entry tells us one atomic dependency fact: entry [j, i] = 1 iff input position
  i participates in producing output position j. Equivalently: think of the Jacobean as the characteristic
  function of a _dependency relation_ between inputs and outputs. The relational perspective is nice because
  it doesn't require us to decide between Galois connections or conjugate pairs at all: we can think about
  individual edges (with that information combining additively).

### §1.2

- Perhaps reframe as an analogy between (Galois-slicing-style) _dependency analysis_ and AD, rather than
  Galois slicing per se; use the matrix intuition to lead into the analogy. For dependency analysis:
  - Every value has a lattice of approximations given by the powerset of the set of positions in the value
  - Every program has a forward approximation map that preserves joins (not meets, at this stage) and also a
  backwards map that also preserves joins.
  - For dependency analysis, these forward and backward maps are related by forming a _conjugate pair_.
    Because powersets have negation, we can also frame this as a Galois connection.
- After the bullet-list analogy, perhaps unpack the correspondence more precisely by outlining how both AD and
  this kind of dependency analysis can be understood in terms of linear maps (matrices), in one case between
  finite-dimensional vector spaces, in the other between Boolean semimodules, with composition as matrix
  multiplication, and linearity corresponding to +-preservation or ∨-preservation.
- A subtlety [can perhaps defer]: in AD, the forward map is usually "given" and the backwards map obtained by
  transposition, whereas in dependency analysis it is (arguably) more natural to think of the backwards map as
  given and the transpose as giving the forward map (but involutivity makes this just a matter of
  presentation).

### §2.2

- The framing in §1.2 introduced conjugate pairs and Galois connections as alternative presentations of the
  same data. But that's only valid in the Boolean setting. More generally, we might want to consider when
  sufficient conditions arise for the existence of backwards join-preserving maps, given some properties of a
  forwards map.
- After the discussion about how operational reasoning about sequentiality (meet-preservation, cm, etc) can
  establish the existence of a join-preserving backward map, perhaps make the point that these meet-preserving
  forward maps may not actually be that useful independently. In Example 2.6 (Interval and Maximal Elements),
  use the _conjugate_ forward map (which preserves joins, not meets) to illustrate, showing addᵀ computes
  [4/5, 1], whereas add⁎ computes [1/2, 3/2], which is lower in the information order

### §3

- The L-poset/stable functions point might be a distraction given that the Fam(C) motivation that comes later
  anyway in terms of providing coproducts (distinct from products in the underlying C) and Cartesian closure.
  Moreover later (end of 3.1) we hedge Proposition 3.3 with a caveat about the significance of Stable and CM
  Maybe instead focus on why categories of relations or matrices and why they are unsuitable for interpreting
  programs (products and coproducts coincide)
- Rather than LatGal and Fam(LatGal), maybe LatConj and Fam(LatConj) is the preferred model
- §3 onwards can focus on Fam(JoinSLat), with JoinSLat (like MeetSLat) having all small limits

### §3.3.2 Lifting Monad

- I'm not sure how to frame the lifting monad L from the matrix perspective. For the tagging monad T(X) = 𝟚 ×
  X, the new bit and the underlying value are independent (which comes with its own problems, as you've
  alluded to). However the independence means we can think of T as just adding another column to the relevant
  matrix. For L(X), there's a constraint such that if you're at the new ⊥ element, then you have no slicing
  information at all about X. So L(𝟚^k) is not 𝟚^(k+1) and probably isn't an object of Mat(𝟚) at all.
  Perhaps we need to say something about how the matrix perspective generalises, maybe to data structures with
  "dependent indices" that allow us to specify that if you're at the ⊥ shape then there are no positions.
  (https://mat.uab.cat/~kock/cat/polynomials.pdf?)

### §4

- I'm wondering if Moggi's CBN translation is actually what we need here. For sums the intuition feels wrong;
  for products and functions, the structure feels wrong. For sums, we add approximation points at the root of
  each summand; although this is isomorphic (because of extensivity?) to adding a single approximation point
  at the sum itself, the latter feels closer to what we mean: a bottom value of type σ + τ hasn't (at the
  fibre level) committed to either inl or inr (which is why any attempt to pattern-match that value must also
  be bottom). For products the structure actually feels wrong; we don't want to add two additional
  approximation points. If we assume each component of the pair already has an appropriate fibre, then we just
  need one additional tag for the pair itself, to distinguish "unused pair" from "pair of unused". And for
  functions similar thought applies. So if the goal of the translation is to recover something similar to
  Galois slicing, perhaps we want something that just adds a tag at each type former, i.e.《σ》= T(1), 《σ →
  τ》 = T(《σ》 → 《τ》), etc.
