with Switch.Val1;
with Switch.Val2;
with Switch.Val3;
package body Switch
--# own State is in Switch.Val1.State,
--#              in Switch.Val2.State,
--#              in Switch.Val3.State;
is

   subtype Value is Integer range -1 .. 1;
   subtype Score is Integer range -3 .. 3;


   function ReadValue return Reading
   --# global in Val1.State;
   --#        in Val2.State;
   --#        in Val3.State;
   is
      A, B, C : Reading;

      --  Embedded package to provide the capability to synthesize three inputs
      --  into one.
      --# inherit Switch;
      package Conversion
      is

         function Convert_To_Reading
            (Val_A : Switch.Reading;
             Val_B : Switch.Reading;
             Val_C : Switch.Reading) return Switch.Reading;

      end Conversion;

      package body Conversion
      is

         type ConvertToValueArray is array (Switch.Reading) of Switch.Value;
         type ConvertToReadingArray is array (Switch.Score) of Switch.Reading;
         ConvertToValue : constant ConvertToValueArray := ConvertToValueArray'(Switch.on => 1,
                                                                         Switch.unknown => 0,
                                                                         Switch.off => -1);

         ConvertToReading : constant ConvertToReadingArray :=
                                      ConvertToReadingArray'(-3 .. -2 => Switch.off,
                                                             -1 .. 1  => Switch.unknown,
                                                             2 ..3    => Switch.on);

         function Convert_To_Reading
            (Val_A : Switch.Reading;
             Val_B : Switch.Reading;
             Val_C : Switch.Reading) return Switch.Reading
         is
         begin

            return ConvertToReading (ConvertToValue (Val_A) +
                   ConvertToValue (Val_B) + ConvertToValue (Val_C));
         end Convert_To_Reading;

      end Conversion;

   begin
       A := Val1.Read;
       B := Val2.Read;
       C := Val3.Read;
       return Conversion.Convert_To_Reading
                (Val_A => A,
                 Val_B => B,
                 Val_C => C);
   end ReadValue;

end Switch;
