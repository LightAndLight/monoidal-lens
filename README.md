# Monoidal Category Lenses

I learned about this from
[Ed Kmett's "Monad Transformer Lenses" talk](https://www.youtube.com/watch?v=Bxcz23GOJqc).

The gist of it is that you have a type `Optic p s t a b` such that
`Lens = Optic (,)` and `Prism = Optic Either`. `Optic` is parameterised over
tensors in the category `Hask`.

A `Tensor` is some type `T :: * -> * -> *`, that has:
* a unit `U :: *`
* associativity isomorphism `T a (T b c) <-> T (T a b) c`
* left identity isomorphism `T U a <-> a`
* right identity isomorphism `T a U <-> a`
* `bimap :: Bifunctor t => (a -> c) -> (b -> d) -> t a b -> t c d`
