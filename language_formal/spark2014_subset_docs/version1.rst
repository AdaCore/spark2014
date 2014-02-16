Version 1
=========

.. admonition:: Contact 

   `Zhi Zhang <zhangzhi@k-state.edu>`__

.. note::
   
   Language feature changes from the previous version (Version 0) are 
   annotated with either [**KSU**] or [**CNAM**], which indicates the team
   responsible for adding the language features.
   
   * **CNAM** team: Pierre Courtieu, Maria Virginia Aponte, Tristan Crolard

   *  **KSU** team: `Zhi Zhang <zhangzhi@k-state.edu>`__,
      `Jason Belt <belt@k-state.edu>`__,
      and `Robby <zhangzhi@k-state.edu>`__.
   
2. Lexical elements:

* identifiers (`2.3 <http://www.ada-auth.org/standards/12rm/html/RM-2-3.html>`_), obviously
* for literals: only integer literals (`2.4 <http://www.ada-auth.org/standards/12rm/html/RM-2-4.html>`_)

3. Declarations and types:

* Boolean (`3.5.3 <http://www.ada-auth.org/standards/12rm/html/RM-3-5-3.html>`_)
* Integer (`3.5.4 <http://www.ada-auth.org/standards/12rm/html/RM-3-5-4.html>`_ (11))
  
  - One would also need universal_integer (`3.4.1 <http://www.ada-auth.org/standards/12rm/html/RM-3-4-1.html>`_ 6/2); as there would be no
    derivation in the minimal subset, it may be identified to Integer for
    the moment

* Array Types declarations  (`3.6 <http://www.ada-auth.org/standards/12rm/html/RM-3-6.html>`_) [**KSU**]
  
  - now we only consider the Array types that use range directly in their
    type definition to avoid introducing subtypes, 
    e.g. `type A is Array(1..10) of Integer`
  - and now we only consider simple one dimension array without nested array 
    or records
    
* Record Types declarations (`3.8 <http://www.ada-auth.org/standards/12rm/html/RM-3-8.html>`_) [**KSU**]
  
  - now we only consider simple record types without nested array or record
  
* Only object declarations (`3.3.1 <http://www.ada-auth.org/standards/12rm/html/RM-3-3-1.html>`_ (5/2)), not aliased
  
  - with only one defining identifier in the defining_identifier_list
    (although that does not make a difference at the AST level)
  
  - both local and global procedure declaration [**CNAM**]

4. Names and expressions:

* for names (`4.1 <http://www.ada-auth.org/standards/12rm/html/RM-4-1.html>`_): 

  - identifier (`2.3 <http://www.ada-auth.org/standards/12rm/html/RM-2-3.html>`_)
  - indexed_component  (`4.1.1 <http://www.ada-auth.org/standards/12rm/html/RM-4-1-1.html>`_) [**KSU**]
  - selected_component (`4.1.3 <http://www.ada-auth.org/standards/12rm/html/RM-4-1-3.html>`_) [**KSU**]
  - function_call      (`6.4 <http://www.ada-auth.org/standards/12rm/html/RM-6-4.html>`_)   [**CNAM**]
  
* for literals (`4.2 <http://www.ada-auth.org/standards/12rm/html/RM-4-2.html>`_): only integer literals
* for aggregate (`4.3 <http://www.ada-auth.org/standards/12rm/html/RM-4-3.html>`_) [**KSU**]

  - record aggregate (`4.3.1 <http://www.ada-auth.org/standards/12rm/html/RM-4-3-1.html>`_) with named associations, 
    e.g. (Day => 1, Month => Feb, Year => 2014) 
    
    (all positional associations can be translated to named association)
    
  - array aggregate  (`4.3.3 <http://www.ada-auth.org/standards/12rm/html/RM-4-3-3.html>`_) with named associations,
    e.g. Array'(1 | 2 | 10 => 1, others => 0) 
    
    (all positional associations can be translated to named association)
  
* operators: non-short-circuit logical (`4.5.1 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-1.html>`_), 
  relational (`4.5.2 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-2.html>`_),
  adding (`4.5.3 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-3.html>`_, 
  `4.5.4 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-4.html>`_), 
  multiplying (`4.5.5 <http://www.ada-auth.org/standards/12rm/html/RM-4-5-5.html>`_) operators
  
  - mod, rem and exponentiation are not included

5. Statements:

* Assignments (`5.2 <http://www.ada-auth.org/standards/12rm/html/RM-5-2.html>`_)
  
  - now we only consider identifier, indexed_component without nested array 
    and selected_component without nested array or nested record as left 
    hand side variables
    
* if statements (`5.3 <http://www.ada-auth.org/standards/12rm/html/RM-5-3.html>`_) without else / elsif
* while loops only (`5.5 <http://www.ada-auth.org/standards/12rm/html/RM-5-5.html>`_ (8)) with no exit statements
* Loop invariants (SPARK RM `5.5.3 <http://docs.adacore.com/spark2014-docs/html/lrm/statements.html#loop-invariants-variants-and-entry-values>`_)

6. Subprograms:

* Only procedure bodies (`6.1 <http://www.ada-auth.org/standards/12rm/html/RM-6-1.html>`_-`6.3 <http://www.ada-auth.org/standards/12rm/html/RM-6-3.html>`_)
  that are the initial declaration of the subprogram 
  (and not the completion: leaving "explicit" declarations out of the subset for now)
* IN, OUT and IN OUT parameters (`6.2 <http://www.ada-auth.org/standards/12rm/html/RM-6-2.html>`_)
* Subprogram Calls (`6.4 <http://www.ada-auth.org/standards/12rm/html/RM-6-4.html>`_) [**CNAM**]
* Pre and Post aspect (`6.1.1 <http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html>`_ (2/3) and (4/3))

  Note that a subprogram unit has an implicit spec unit, so it can be
  mentioned in a with-clause. Again, of no interest at AST level

7. Packages:

* Out for the first subset; meaning that only subprograms would be
  allowed as compilation units

8. Visibility rules:

* With the previous restriction, this chapter ends up becomes trivial
