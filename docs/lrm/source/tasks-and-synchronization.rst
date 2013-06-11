Tasks and Synchronization
=========================

Concurrent programs require the use of different specification and verification
techniques from sequential programs. For this reason, tasks, protected units and
objects, and synchronization features are currently excluded from |SPARK|.

.. todo:: RCC: The above text implies that |SPARK| does not support Ada.Calendar,
   which is specified in RM 9.6. SPARK 2005 supports and prefers Ada.Real_Time
   and models the passage of time as an external "in" mode protected own variable.
   Should we use the same approach in |SPARK|? Discussion under TN [LB07-024].
   To be completed in the Milestone 4 version of this document.

.. todo:: Add Tasking. To be completed in a post-Release 1 version of this document.
