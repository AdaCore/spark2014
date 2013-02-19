
.. _context:

Context
=======


This section presents the extended context diagram of the |SPARK| project. Identifying all direct and indirect stakeholders in the project and then considering requirements specific to each stakeholder helps to ensure a complete set of requirements are elicited.

.. graphviz::

   digraph context {
      spark [label="SPARK 2014"]
      sparkPro [label="SPARK 2005"]
      prooftools [label="External Proof Tools"]
      DO178C [label="DO-178C"]
      Ada2012 [label="Ada 2012"]
      Ada2005 [label="Ada 2005"]
      AdacoreTools [label="AdaCore tools"]
      OtherTools [label="3rd party tools"]

      AviationCustomers [label="Aviation Industry"]
      SecurityCustomers [label="Security Industry"]
      spark -> DO178C [label=" Supports", fontsize=7]
      Ada2005 -> Ada2012 [label=" Developed from", fontsize=7]
      Ada2005 -> sparkPro [label=" Uses", fontsize=7]
      Ada2012 -> spark [label=" Uses", fontsize=7]
      sparkPro -> spark [label=" Developed from", fontsize=7]
      AdaCore -> spark [label=" Develops", fontsize=7]
      AdaCore -> AdacoreTools [label=" Develops", fontsize=7]
      Customers -> AdacoreTools [label=" Use", fontsize=7]
      Customers -> OtherTools [label=" Use", fontsize=7]
      OtherTools -> spark [label=" Integrte with", fontsize=7]
      OtherTools -> sparkPro [label=" Integrte with", fontsize=7]
      Altran -> spark [label=" Develops", fontsize=7]
      Altran -> Customers [label=" Provides services to", fontsize=7]
      Academia -> spark [label=" Use", fontsize=7]
      Academia -> sparkPro [label=" Use", fontsize=7]
      Customers -> spark [label=" Use", fontsize=7]
      Customers -> sparkPro [label=" Use", fontsize=7]
      Customers -> Ada2005 [label=" Use", fontsize=7]
      AviationCustomers -> DO178C [label=" Use", fontsize=7]
      AviationCustomers -> Customers [label=" Member of", fontsize=7]
      SecurityCustomers -> Customers [label=" Member of", fontsize=7]
      SecurityCustomers -> prooftools [label=" Use", fontsize=7]
      sparkPro -> prooftools [label=" Supports", fontsize=7]
      spark -> prooftools [label=" Supports", fontsize=7]
   }

