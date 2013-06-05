Tasks and Synchronization
=========================

Concurrent programs require the use of different specification and verification
techniques from sequential programs. For this reason, tasks, protected units and
objects, and synchronization features are currently excluded from |SPARK| 
but are targeted to be included in Release 2 of the |SPARK| language and toolset.

.. todo:: RCC: The above text implies that |SPARK| does not support Ada.Calendar,
   which is specified in RM 9.6. SPARK 2005 supports and prefers Ada.Real_Time
   and models the passage of time as an external "in" mode protected own variable.
   Should we use the same approach in |SPARK|? Discussion under TN [LB07-024].
   To be completed in the Milestone 3 version of this document.

.. todo:: Add Tasking. Target: release 2 of |SPARK| language and toolset.
