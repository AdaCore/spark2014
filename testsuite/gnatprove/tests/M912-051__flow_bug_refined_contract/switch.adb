with Switch.Val1;
with Switch.Val2;
with Switch.Val3;

package body Switch
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
                            -1 .. 1 => unknown,
                            2 ..3 => on);

   procedure ReadValue (Value : out Reading)
   with Refined_Global  => (Input => (Val1.State,
                                      Val2.State,
                                      Val3.State)),
        Refined_Depends => (Value => (Val1.State,
                                      Val2.State,
                                      Val3.State))
   is
      A, B, C : Reading;
   begin
       Val1.Read (A);
       Val2.Read (B);
       Val3.Read (C);
       Value := ConvertToReading (ConvertToValue (A) +
                                  ConvertToValue (B) + ConvertToValue (C));
   end ReadValue;

end Switch;
