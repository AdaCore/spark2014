.. _Overview of SPARK Language:

****************************
Overview of |SPARK| Language
****************************

This chapter provides an overview of the |SPARK| language, detailing for each
feature its consequences in terms of execution and formal verification. This is
not a reference manual for the |SPARK| language, which can be found in:

* the Ada Reference Manual (for Ada features), and
* the SPARK Reference Manual (for SPARK-specific features)

More details on how |GNAT Pro| compiles |SPARK| code can be found in the |GNAT
Pro| Reference Manual.

|SPARK| can be seen as a large subset of Ada with additional
aspects/pragmas/attributes. It includes in particular:

* rich types (subtypes with bounds not known statically, discriminant records,
  subtype predicates, access types)
* flexible features to structure programs (function and operator
  overloading, early returns and exits, raise statements)
* code sharing features (generics, expression functions)
* object oriented features (tagged types, dispatching)
* concurrency features (tasks, protected objects)

In the rest of this chapter, the marker [Ada 2005] (resp. [Ada 2012] or [Ada
202X]) is used to denote that a feature defined in Ada 2005 (resp. Ada 2012 or
Ada 202X) is supported in |SPARK|, and the marker [Ravenscar/Jorvik] is used to
denote that a concurrency feature from Ada which belongs to the Ravenscar or
Jorvik profiles is supported in |SPARK|.  The marker [|SPARK|] is used to
denote that a feature is specific to |SPARK|. Both the |GNAT Pro| compiler and
|GNATprove| analyzer support all features listed here.

Some code snippets presented in this section are available in the example
called ``gnatprove_by_example`` distributed with the |SPARK| toolset. It can be
found in the ``share/examples/spark`` directory below the directory where the
toolset is installed, and can be accessed from the IDE (either GNAT Studio or
GNATBench) via the :menuselection:`Help --> SPARK --> Examples` menu item.

.. only : : core

   .. toctree::
      :maxdepth: 2

      source/language_restrictions
      source/subprogram_contracts

.. only:: full

   .. toctree::
      :maxdepth: 2

      source/language_restrictions
      source/subprogram_contracts
      source/package_contracts
      source/type_contracts
      source/specification_features
      source/assertion_pragmas
      source/overflow_modes
      source/object_oriented_programming
      source/access
      source/concurrency
      source/spark_libraries
