This program searches for a given value in an ordered array. The postcondition
of the main function `Binary_Search` expresses that the search is successful
if-and-only-if the array contains the value searched, and if so the index
returned is one at which the array contains this value. GNATprove proves all
checks on this program. The version with an unconstrained array is the same
as the one presented in the section on How to Write Loop Invariants of the
SPARK User's guide, and used in a series of two articles published by Johannes
Kanig in Electronic Design to compare dynamic and static verification
techniques (see [This article in the AdaCore
blog](http://blog.adacore.com/testing-static-formal)).
