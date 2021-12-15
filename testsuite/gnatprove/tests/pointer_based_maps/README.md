This program features a pointer-based implementation of a map as a singly-linked
list of pairs. The example is described in a [blog
post](https://blog.adacore.com/pointer-based-data-structures-in-spark).  It
explains how local borrowers and observers can be used to traverse a recursive
data-struture, traversal functions, and how to use pledges to supply
information about borrowed objects.

In addition to the subprograms presented in the blog post, the example also
provides an extended version of `Replace_Element`. It is completely specified,
using the `Iterable` aspect to allow quantification over keys included in a
map.
