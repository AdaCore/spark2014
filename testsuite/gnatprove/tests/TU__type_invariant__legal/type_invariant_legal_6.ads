--  TU: 6. Invariant checking is extended to include checking the incoming
--  parameter values of any calls from code where invariant-violating values
--  may be available to subprograms where invariant-violating values are
--  intended to be unavailable.

package Type_Invariant_Legal_6 with SPARK_Mode is

   type T is private;

   function Pub (X : T) return Integer;
   procedure Pub_In (X : T);
   procedure Pub_Out (X : out T);
   procedure Pub_In_Out (X : in out T);

private
   type T is new Natural with Type_Invariant => T /= 0; -- @INVARIANT_CHECK:FAIL

end Type_Invariant_Legal_6;
