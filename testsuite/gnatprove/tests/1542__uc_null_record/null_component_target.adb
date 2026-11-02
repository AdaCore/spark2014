with Ada.Unchecked_Conversion;

procedure Null_Component_Target with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Empty is null record with Size => 0;
   type Target is record
      Value   : Byte;
      Nothing : Empty;
   end record with Size => 8, Alignment => 1;
   for Target use record
      Value   at 0 range 0 .. 7;
      Nothing at 1 range 0 .. -1;
   end record;

   function Convert is new Ada.Unchecked_Conversion (Byte, Target);

   Y : constant Target := Convert (1);
begin
   pragma Assert (Y.Value = 1);
   pragma Assert (Y.Nothing = (null record));
end Null_Component_Target;
