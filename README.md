# MultiWalk

This library provides functionality for traversing data types recursively,
acting on multiple types during the same traversal. In spirit, it is similar to
the `Walk` type class from `Pandoc.Walk`, but generalizes it by allowing
multiple types to be targeted by the traversal. Also, by default it only
requires an `Applicative` constraint on the action, making it suitable for
situations where you don't have a `Monad` (for instance, traversing within a
composition of monads).

Say, for instance, you want to query all code snippets from a Pandoc document,
including both `Inline` and `Block` ones, such that the list of results is *in
the same order* as they appear in the document. There is no way to do this with
Pandoc's `Walk` type class, because it only supports querying or walking with
one type at once. With MultiWalk you are able to do this with a single query
function that targets both types, and it'll look something like this:

```haskell
multi :: Block -> [Text]
multi = buildMultiQ @PTag $ \sub list ->
    list ?> blks sub
         ?> inls sub
  where
    blks _ (CodeBlock _ c) = [c]
    blks f x = f x
    inls _ (Code _ c) = [c]
    inls f x = f x
```

(note, however, that this library does not ship with default instances for
Pandoc, so you will have to define them yourself. You can find a basic Pandoc
instance for reference, and the function above, in `Benchmark.hs` inside the
test directory.)

Another use case is when you want to modify a data type, perhaps targeting
multiple subtypes, and you want to do that inside a functor that is
`Applicative` but not a `Monad`. Such functors may sound unusual, but one of the
interesting places where they appear are in composition of monads, which need
not be a monad itself. 

You can find a use of such monad compositions in my other library
[here](https://github.com/lucasvreis/org-mode-hs/blob/main/org-exporters/src/Org/Exporters/Processing/InternalLinks.hs).
It's used for resolving cross-references inside documents inside the functor
`Compose M F`, where `M` is a state monad which holds the links it has found so
far, and `F` is a reader which receives the _final, future state_ (that will
only be ready _at the end of the computation_). In this way I can walk across
the document only once, registering and applying cross references at the same
time. Note that this is composition is semantically different from using monad
transformers, because they would require the reader state to be supplied before
the final state is available.
