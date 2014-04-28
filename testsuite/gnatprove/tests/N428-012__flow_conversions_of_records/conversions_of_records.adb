with Ada.Unchecked_Conversion;

package body Conversions_Of_Records
  with SPARK_Mode
is
   function To_Rec_B is new Ada.Unchecked_Conversion (Source => Rec_A,
                                                      Target => Rec_B);

   procedure Conv (R  : in     Rec_A;
                   X1 :    out Integer;
                   X2 :    out Integer)
   is
   begin
      X1 := Rec_B (R).X;
      X2 := To_Rec_B (R).X;
   end Conv;
end Conversions_Of_Records;
