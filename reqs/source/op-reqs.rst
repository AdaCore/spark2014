
Operational Reqs
================

See "Product Features" in https://docs.google.com/document/d/1DP5kKBWL5MdfrHmCFt2CEDJc3n6JfSHvGNGjwPz9j7U/edit#


:Req Id: A req name
:Description: A description
   over multiple lines
:Rationale: A Rationale
   
   more text


The following requirements have been derived primarily from the use cases defined later in this document (see :ref:`Use Cases`.).


1a(i)	Detection of undefined behaviour	
1a(ii)	Dataflow analysis	
1b(i)	Subset checking 	legality rules and (optional) restrictions in new LRM
1b(ii)	Static verification	static semantics in the new LRM
2a	Verification of intended information flow	
2b	Security and safety policy checking	Includes advanced features such as refined info flow and slicing
3a	Automated proof of AoRTE	
3b	Automated proof of simple properties (safety, security,)	To show isolated, key functional properties, such as safety invariants
3c	Complex and/or manual proofs Includes manual proof assistants and gateways to other proof tools.

Used to verify code against a functional spec
4	Verification of multi-task programs	
5	Unit Test	Unit testing in the HiLite sense ie. as a fallback from automated proof. (Is there a better name for this eg Verification by unit test?)


Copy in Patrice's reqs


