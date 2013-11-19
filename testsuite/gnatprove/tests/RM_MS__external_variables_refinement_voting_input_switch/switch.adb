with Switch.Val1,
     Switch.Val2,
     Switch.Val3;

package body Switch
   -- State is refined onto three states, each of which has properties
   --  Volatile and Input
  with SPARK_Mode,
       Refined_State => (State => (Switch.Val1.State,
                                   Switch.Val2.State,
                                   Switch.Val3.State))
is
   subtype Value is Integer range -1 .. 1;
   subtype Score is Integer range -3 .. 3;
   type ConvertToValueArray is array (Reading) of Value;
   type ConvertToReadingArray is array (Score) of Reading;

   ConvertToValue : constant ConvertToValueArray :=
     ConvertToValueArray'(on => 1,
                          unknown => 0,
                          off => -1);
   ConvertToReading : constant ConvertToReadingArray :=
     ConvertToReadingArray'(-3 .. -2 => off,
                            -1 .. 1  => unknown,
                             2 .. 3  => on);

   function ReadValue return Reading
     with Refined_Global => (Input => (Val1.State, Val2.State, Val3.State))
   is
      A, B, C : Reading;
   begin
      A := Val1.Read;
      B := Val2.Read;
      C := Val3.Read;
      return ConvertToReading (ConvertToValue (A) +
        ConvertToValue (B) + ConvertToValue (C));
   end ReadValue;
end Switch;
