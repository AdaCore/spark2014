Version 0
=========

.. admonition:: Contact 

   `Jerome Guitton <guitton@adacore.com>`__

2. Lexical elements:

* identifiers (`2.3 <http://www.ada-auth.org/standards/12rm/html/RM-2-3.html>`_), obviously
* for literals: only integer literals (`2.4 <http://www.ada-auth.org/standards/12rm/html/RM-2-4.html>`_)

3. Declarations and types:

* No type declarations; only two types for now
* Boolean (`3.5.3 <http://www.ada-auth.org/standards/12rm/html/RM-3-5-3.html>`_)
* Integer (`3.5.4 <http://www.ada-auth.org/standards/12rm/html/RM-3-5-4.html>`_ (11))
 
  - One would also need universal_integer (`3.4.1 <http://www.ada-auth.org/standards/12rm/html/RM-3-4-1.html>`_ 6/2); as there would be no 
    derivation in the minimal subset, it may be identified to Integer for
    the moment

* Only object declarations (`3.3.1 <http://www.ada-auth.org/standards/12rm/html/RM-3-3-1.html>`_ (5/2)), not aliased
  
  - with only one defining identifier in the defining_identifier_list
    (although that does not make a difference at the AST level)

4. Names and expressions:

* for literals (`4.2 <http://www.ada-auth.org/standards/12rm/html/RM-4-2.html>`_): only integer literals
* operators: non-short-circuit logical (`4.5.1 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-1.html>`_), 
  relational (`4.5.2 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-2.html>`_),
  adding (`4.5.3 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-3.html>`_, 
  `4.5.4 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-4.html>`_), 
  multiplying (`4.5.5 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-5.html>`_) operators
 
  - mod, rem and exponentiation are not included

5. Statements:

* Assignments (`5.2 <http://www.ada-auth.org/standards/12rm/html/RM-5-2.html>`_)
* if statements (`5.3 <http://www.ada-auth.org/standards/12rm/html/RM-5-3.html>`_) without else / elsif
* while loops only (`5.5 <http://www.ada-auth.org/standards/12rm/html/RM-5-5.html>`_ (8)) with no exit statements
* Loop invariants (SPARK RM `5.5.3 <http://docs.adacore.com/spark2014-docs/html/lrm/statements.html#loop-invariants-variants-and-entry-values>`_)

6. Subprograms:

* Only procedure bodies (`6.1 <http://www.ada-auth.org/standards/12rm/html/RM-6-1.html>`_-`6.3 <http://www.ada-auth.org/standards/12rm/html/RM-6-3.html>`_) 
  that are the initial declaration of the subprogram (and not the completion: leaving "explicit" declarations
  out of the subset for now)
* Only IN and OUT parameters, no IN OUT (`6.2 <http://www.ada-auth.org/standards/12rm/html/RM-6-2.html>`_)
* Pre and Post aspect (`6.1.1 <http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html>`_ (2/3) and (4/3))
  
  - Note that a subprogram unit has an implicit spec unit, so it can be
    mentioned in a with-clause. Again, of no interest at AST level

7. Packages:

* Out for the first subset; meaning that only subprograms would be
  allowed as compilation units

8. Visibility rules:

* With the previous restriction, this chapter ends up becomes trivial

