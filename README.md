# MultiWalk

This library provides functionality for traversing data types recursively,
acting on multiple types during the same traversal. In spirit, it is similar to
the `Walk` type class from `Pandoc.Walk`, but generalizes it by allowing
multiple types to be targeted by the traversal. Also, by default it only
requires an `Applicative` constraint on the action, making it suitable for
situations where you don't have a `Monad` (for instance, traversing within a
composition of monads --- read more about a use case below).

## Writing queries
*todo*
## Applicative traversals

*todo*
