"""Manage lattices attributes

This package allows to handle sets with attributes taking values
in the same lattice.

Given a set A, we say that it takes values into the lattice LATTICE if
there exists an application A[a] from A to LATTICE.

           A
           |
           | A[a]
           V
        LATTICE

We call 'a' the name of the attribute. Examples of such lattice
attributes are: lines ranges, coverage status...

A can be seen as a discrete category, in which case A[a] is a
simplistic functor; what is more interesting is to extends this
functor to the category P(A) of subset of A, which takes the same
value on singletons.

    P(A)
     |
     |
     | P(A)[a]
     |
     |
     V
  LATTICE


Indeed P(A) is itself a lattice, and we would define P(A)[a]
as:

  for all pa in P(A),
    P(A)[a](pa) = join {A[a](x), x in pa}

From there, we can easily define an inversion as an arrow that goes
the other way around:

    P(A)
     ^
     |
     | inv(A)[a]
     |
     |
     |
  LATTICE

as:

 inv(A)[a](v) = {x in A such that A[a](x) in v}

This functor is the inversion of A[a] if and only if P(A)[a] is
injective.  For the other case, imagine an example where 'LATTICE' is
the set of slocs ranges, 'A' the set of subprograms, 'A[a]' the
function that returns the sloc of ranges associated to a and 'nesting',
'nested' two subprograms such that A[a](nested) is in A[a](nesting).
In this case, '(inv(A)[a] . P(A)[a]) (nesting)' will also contain
'nested'. However, we have:

  inv(A)[a] . P(A)[a] . inv(A)[a] = inv(A)[a]
  P(A)[a] . inv(A)[a] . P(A)[a] = P(A)[a]

inv(A)[a] is the right adjoint of P(A[a]), meaning that it returns the
minimal superset of nesting.

We now consider two objects 'From', 'To' having a lattice attribute 'a' and
an arrow F : From -> To

                      F
             From ---------> To
               \            /
                \          /
                 \        /
          From[a] \      / To[a]
                   \    /
                    \  /
                     ||
                     VV
                   LATTICE

The purpose of this module is to provides way to compute maximal/minimal
solutions for such a diagram, assuming that two arrows are known and returning
the last one. Depending on this last one, here is the name that we give to
each solution
* From[a]: composition;
* To[a]: join and meet (i.e. minimal and maximal extensions);
* F: (maximal) inclusion and (minimal) superset.

"""

from internal import sets

class Inclusion(sets.Arrow):
    """Build the maximal inclusion from attribute values in a common lattice

    Return an arrow representing the maximal inclusion of one object into the
    other. In categorical terms, from the basic diagram:

                      F
             From ---------> To
               \            /
                \          /
                 \        /
          From[a] \      / To[a]
                   \    /
                    \  /
                     ||
                     VV
                   LATTICE

    This builds F from From[a] and To[a] as the Left Kan extension of
    the following diagram:

                    inv(From)[a]
            LATTICE ---------> P(From)
               \
                \
                 \
       inv(To)[a] \
                   \
                    \
                     V
                    P(To)

    Example: if the main object contains two ranges  P1 and P2, and the
    subobjects two VC1, VC2, VC3, this will build the following inclusion
    arrow:

               P1                   P2
    ......[---------].......[----------------]..........
                 ^             ^      ^
                 |             |      |
    ...........[---].........[---]..[----]..............
                VC1           VC2     VC3

    In other words, it will return the continuous map

       in_object : subobject -> object

    ...such for each x in subobject, x is included into in_object(x)
    i.e. the following diagram commutes:

                      in_object
       subobject ...................> object
           |                          |
           | attribute                | attribute
           V                          V
   subobject[attribute] -------> object[attribute]
                           IN

    e.g. in_object(VC1) = P1 in our example,
         as in_object(VC1)[attribute] <= P1[attribute]

    If several solution exists, it will return the minimal one. e.g. if
    there is some nesting in object:

                 P1
    .....[----------------]..........
            P2      ^
    ......[---].....|................
            ^       |
            |       |
    .......[-]....[---]..............
           VC2     VC1

    ... then VC1 will be in P1, and VC2 in P2.
    """

    def __init__(self, lattice, object):
        self.lattice = lattice
        self.object = object

    def follow(self, object, key):
        result = None
        result_value = self.lattice.value_max()
        for outer_key in self.object.content():
            if self.lattice.is_in(object, key, self.object, outer_key):
                candidate = self.object.follow("NAME", outer_key)
                candidate_value = self.lattice.follow(self.object, outer_key)
                if self.lattice.value_is_in(candidate_value, result_value):
                    result_value = candidate_value
                    result = candidate
        return result


class Join(sets.Arrow):
    """Build the attribute values as a join

    Return an arrow representing the minimal extension of an attribute
    of one object into an other. In categorical terms, from our
    canonical diagram:

                      F
             From ---------> To
               \            /
                \          /
                 \        /
          From[a] \      / To[a]
                   \    /
                    \  /
                     ||
                     VV
                   LATTICE

    It will return To[a] as a left Kan extension of the other arrows.
    In other words, it will return the map

       attribute : object -> object[attribute]

    ...such for each x in subobject, x[attribute] is the minimal value
    such that in_object(x)[attribute] <= x[attribute]
    i.e. object[attribute] is the minimal object for which
    the following diagram commutes:

                      in_object
       subobject  ----------------> object
           |                          .
           | attribute                . attribute
           V                          V
    subobject[attribute] -------> object[attribute]
                         IN

    """
    def __init__(self, lattice, subobject, in_object_key):
        self.lattice = lattice
        self.subobjects = [subobject]
        self.in_object_key = in_object_key

    def add(self, subobject):
        self.subobjects.append(subobject)

    def follow(self, object, key):
        result = self.lattice.empty_set()
        for subobject in self.subobjects:
            for subobj_key in subobject.content():
                attribute = subobject.follow(self.in_object_key, subobj_key)
                if attribute == key:
                    result = \
                        self.lattice.value_join \
                        (result,
                         self.lattice.follow(subobject, subobj_key))
        return result
