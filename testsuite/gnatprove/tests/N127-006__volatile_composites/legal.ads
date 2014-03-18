package Legal
  with SPARK_Mode => On
is
   --  Tests for volatile variable usages, where the usage should
   --  be legal in SPARK 14.0.2+

   --  In particular, this test illustrates the reading and writing
   --  of volatile composite objects, which are introduced in SPARK 14.0.2+
   --  as a result of adding the fifth bullet below to RM rule 7.1.3(13)

   --  TU: 13. Contrary to the general |SPARK| rule that expression evaluation
   --  cannot have side effects, a read of a Volatile object with the
   --  properties Async_Writers or Effective_Reads set to True is
   --  considered to have an effect when read. To reconcile this
   --  discrepancy, a name denoting such an object shall only occur in
   --  the following contexts:
   --  * as the name on the left-hand side of an assignment statement; or
   --  * as the [right-hand side] expression of an assignment statement; or
   --  * as the expression of an initialization expression of an object
   --    declaration; or
   --  * as an actual parameter in a call to an instance of
   --    Unchecked_Conversion whose result is renamed [in an object renaming
   --    declaration].
   --  * as a prefix of a name which occurs in such a context

   type R is record
      F1 : Integer;
      F2 : Boolean;
   end record;

   type I is range 1 .. 10;

   type AI is array (I) of Integer;

   type AR is array (I) of R;

   V1 : Integer
     with Volatile, Async_Writers;

   V2 : R
     with Volatile, Async_Writers;

   V3 : AI
     with Volatile, Async_Writers;

   V4 : AR
     with Volatile, Async_Writers;


   procedure RV1 (X : out Integer)
     with Global => (Input => V1);

   procedure WV1 (X : in Integer)
     with Global => (Output => V1);



   procedure RV2 (X : out Boolean)
     with Global => (Input => V2);

   procedure WV2 (X : in Boolean)
     with Global => (Output => V2);



   procedure RV3 (X : out Integer)
     with Global => (Input => V3);

   procedure RV3UC (X : out Integer)
     with Global => (Input => V3);

   procedure WV3 (X : in Integer)
     with Global => (Output => V3);



   procedure RV4 (X : out Boolean)
     with Global => (Input => V4);

   procedure WV4 (X : in Boolean)
     with Global => (Output => V4);

   procedure RV4b (X : out Boolean)
     with Global => (Input => V4);



end Legal;
