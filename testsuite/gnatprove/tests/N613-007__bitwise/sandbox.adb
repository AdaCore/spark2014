
package body Sandbox
  with SPARK_Mode
is

   function Shift_Right(Value : Size64_Type; Count : Natural) return Size64_Type
     with
       Import,
       Convention => Intrinsic,
       Global     => null,
       Post       => Shift_Right'Result = Value / (2**Count);

   procedure Split(Whole : in Size64_Type; MSW, LSW : out Size32_Type) is
   begin
      MSW := Size32_Type(Shift_Right(Value => Whole, Count => 32));
      LSW := Size32_Type(Whole and 16#00000000FFFFFFFF#);
   end Split;

end Sandbox;
