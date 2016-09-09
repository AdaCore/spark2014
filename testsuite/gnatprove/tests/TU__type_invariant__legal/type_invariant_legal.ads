--  Check that type invariant is checked where Ada RM imposing a run-time check

package Type_Invariant_Legal with SPARK_Mode is

   type T is private;

   function Pub return T;  --  @INVARIANT_CHECK:FAIL
   function E_Pub return T;  --  @INVARIANT_CHECK:PASS

   procedure Pub_In (X : T);  --  @INVARIANT_CHECK:NONE
   procedure Pub_Out (X : out T);  --  @INVARIANT_CHECK:PASS
   procedure Pub_In_Out (X : in out T);  --  @INVARIANT_CHECK:FAIL

private
   type T is new Natural with Type_Invariant => T /= 0;  --  @INVARIANT_CHECK:FAIL

   function Priv return T with Pre => True;  --  @INVARIANT_CHECK:NONE
   function E_Priv return T;  --  @INVARIANT_CHECK:NONE

   function E_Pub return T is (1);
   function E_Priv return T is (0);

end Type_Invariant_Legal;
