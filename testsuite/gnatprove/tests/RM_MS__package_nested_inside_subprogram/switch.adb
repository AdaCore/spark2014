with Switch.Val1,
     Switch.Val2,
     Switch.Val3;

package body Switch
  --  State is refined onto three states, each of which has properties
  --  Volatile and Input.
  with SPARK_Mode,
       Refined_State => (State => (Switch.Val1.State,
                                   Switch.Val2.State,
                                   Switch.Val3.State))
is
   subtype Value is Integer range -1 .. 1;
   subtype Score is Integer range -3 .. 3;

   function ReadValue return Reading
     with Refined_Global => (Input => (Val1.State, Val2.State, Val3.State))
   is
      A, B, C : Reading;

      --  Embedded package to provide the capability to synthesize three inputs
      --  into one.
      package Conversion is
         function Convert_To_Reading
           (Val_A : Switch.Reading;
            Val_B : Switch.Reading;
            Val_C : Switch.Reading) return Switch.Reading;
      end Conversion;

      package body Conversion is
         type ConvertToValueArray is array (Switch.Reading) of Switch.Value;
         type ConvertToReadingArray is array (Switch.Score) of Switch.Reading;
         ConvertToValue : constant ConvertToValueArray :=
           ConvertToValueArray'(Switch.on => 1,
                                Switch.unknown => 0,
                                Switch.off => -1);

         ConvertToReading : constant ConvertToReadingArray :=
           ConvertToReadingArray'(-3 .. -2 => Switch.off,
                                  -1 .. 1  => Switch.unknown,
                                   2 .. 3  => Switch.on);

         function Convert_To_Reading
            (Val_A : Switch.Reading;
             Val_B : Switch.Reading;
             Val_C : Switch.Reading) return Switch.Reading is
           (ConvertToReading (ConvertToValue (Val_A) +
                              ConvertToValue (Val_B) +
                              ConvertToValue (Val_C)));
      end Conversion;
   begin  --  begin statement of ReadValue function
      A := Val1.Read;
      B := Val2.Read;
      C := Val3.Read;
      return Conversion.Convert_To_Reading
               (Val_A => A,
                Val_B => B,
                Val_C => C);
   end ReadValue;
end Switch;
