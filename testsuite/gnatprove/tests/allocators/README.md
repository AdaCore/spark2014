This program demonstrates how the specification of a SPARK program can be
formalized using an abstract model and how the refinement relation between the
model an its implementation can be verified using GNATprove. It is described
in the article
["Abstract Software Specifications and Automatic Proof of Refinement"](http://blog.adacore.com/uploads/rssrail.pdf)
published at RSSRail 2016 conference.

The example contains three versions of an allocator package. They are specified
in terms of mathematical structures (sequences and sets). The refinement
relation between the mathematical model and the implementation is expressed as a
ghost function `Is_Valid` and enforced through contracts. It can be verified
automatically using GNATprove.

 * `Simple_Allocator` features a naive implementation of the allocator,
   storing the status (available or allocated) of each resource in a big array.
   It is specified using a ghost function `Model` which always returns a
   valid refinement of the allocator's data. The refinement relation is
   verified only once, as a postcondition of the `Model` function. The
   functional contracts on modifying procedures as well as the refinement
   relation are straightforward and can be verified easily at level 2 in
   a few seconds.

 * `List_Allocator` introduces a free list to access more efficiently the
   first available resource. Here not every possible state of the allocator
   data can be refined into a valid model. To work around this problem, the
   model is stored in a global ghost variable which is updated along with the
   allocator's data and the refinement relation is expressed as an invariant
   that must be verified as a postcondition of each modifying procedure. The
   functional contracts on modifying procedures are straightforward but the
   refinement relation is now more complicated, as it needs to account for the
   implementation of the free list. They can be verified at level 4 in less
   than one minute overall.

 * `List_Mod_Allocator` features the same implementation and contracts as
   `List_Allocator`, but its model is returned by a ghost function like in
   `Simple_Allocator` instead of being stored in a global ghost variable. As
   not every possible state of the allocator can be refined into a valid model,
   the refinement relation is not expressed as a postcondition of Model, but as
   an invariant, as in `List_Allocator` and must be verified as a
   postcondition of each modifying procedure. The functional contracts and the
   refinement relation resemble those of `List_Allocator`. However, as we
   don't construct explicitly the new model after each modification, the proof
   of the allocator's functional contracts requires induction, which is beyond
   the reach of automatic solvers. The induction scheme is given here manually
   in an auto-active style through calls to ghost procedures.  The whole
   program can then be verified automatically at level 4 in less than one
   minute overall on an 8-cores machine, or in a few minutes on a single core.
