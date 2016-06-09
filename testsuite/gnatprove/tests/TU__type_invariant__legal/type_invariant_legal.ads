--  Check that type invariant is checked where Ada RM imposing a run-time check

package Type_Invariant_Legal is

   type T is private;

   function Pub return T;
   function E_Pub return T;

   procedure Pub_In (X : T);
   procedure Pub_Out (X : out T);
   procedure Pub_In_Out (X : in out T);

private
   type T is new Natural with Type_Invariant => T /= 0;

   function Priv return T;
   function E_Priv return T;

   function E_Pub return T is (1);  --  @INVARIANT_CHECK:PASS
   function E_Priv return T is (0);  --  @INVARIANT_CHECK:NONE

end Type_Invariant_Legal;
