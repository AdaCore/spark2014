This program searches for a given value in an unordered linked list. The
postcondition of the main function `Search` expresses that the search is
successful if-and-only-if the list contains the value searched, and if so the
cursor returned is one at which the list contains this value. GNATprove
proves all checks on this program.
