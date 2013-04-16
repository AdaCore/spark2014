
Analyse Multiple Models
-----------------------

:ID: UC.AnalyseMultipleModels
:Overview: In certain situations, it is useful to define dual abstract views on the state provided by a given module: one of those views provides an abstraction that makes sense to calling code, while the other is more implementation-focused.
:Target Rel: |rel 1|
:Priority: Required
:Part of: Base Product
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. All preconditions hold from :ref:`uc-analyse-data-flow`, :ref:`uc-analyse-information-flow`
   and ''TBD'' (ref for proof use case).

#. TBD: decide if we want to forbid this use case in retrospective/generative mode and so
   need to impose a restriction to stop that.
   
#. Code base contains packages where it would be useful to define multiple abstract views of the hidden
   state contained within those packages.

Scenario
^^^^^^^^

#. Identify packages where it would be useful to define multiple abstract views of the hidden state
   declared within the package.

#. Define and record multiple abstract views of the same state in tool-readable form and location.

#. Define and record what code files are to be analysed under what view.

#. For each type of abstract view, perform :ref:`uc-analyse-data-flow`, :ref:`uc-analyse-information-flow`
   and ''TBD'' (ref for proof use case). Is there any other analysis to be performed?

#. Manually review corresponding abstract views against each other for consistency.

#. Developer fixes all errors.

#. Repeat steps 3, 4 and 5 until the post-conditions are met.

Scenario Notes
^^^^^^^^^^^^^^

#. In certain cases, the abstract view of hidden state that is most useful and makes most sense
   to client code cannot be supported by standard SPARK refinement, and the semantic gap between it
   and the concrete state in the implementation is too great.
   
#. In such cases, two abstract views are provided. One of those views makes sense to client code
   as discussed above. The
   second view will be an implementation-focused abstraction that indicates how the first abstraction
   is to be implemented though without providing full detail.

#. This second, implementation-focused view is related to the concrete implementation view using
   standard SPARK refinement and can be reviewed manually against the client-focused abstract view
   to ensure consistency between the two abstract views.

#. In SPARK 2005, dual annotations -- for example using - - % with - - # -- are used to introduce
   the two abstract views.

#. This use case is most likely to apply when modelling system boundaries.

#. An example is where multiple types of data item are received down the same physical channel. The
   client-focused abstract view could define one item of state per logical type of data, while the
   implementation-focused abstraction would make clear the implementation was a single channel,
   though without giving details on how that channel was implemented.

Postcondition
^^^^^^^^^^^^^

#. The corresponding abstract views are consistent with each other.

#. The postconditions are met for :ref:`uc-analyse-data-flow`, :ref:`uc-analyse-information-flow`
   and ''TBD'' (ref for proof use case).

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. All exceptions and alternative flows are covered by those under the use cases
   :ref:`uc-analyse-data-flow`, :ref:`uc-analyse-information-flow`
   and ''TBD'' (ref for proof use case).

Special Requirements
^^^^^^^^^^^^^^^^^^^^
None


