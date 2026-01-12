with Ada.Unchecked_Conversion;
procedure Test with SPARK_Mode is
   type Int_8 is range - 128 .. 127;
   type Mod_8 is mod 256 with
     Annotate => (GNATprove, No_Bitwise_Operations);
   --  Use No_Bitwise_Operations to disable precise handling of UC

   function Int_To_Mod is new Ada.Unchecked_Conversion (Int_8, Mod_8);

   function Mod_To_Int is new Ada.Unchecked_Conversion (Mod_8, Int_8);

   procedure Test (X : Int_8; Y : Int_8) is
   begin
      pragma Assert (if Int_To_Mod (X) = Int_To_Mod (Y) then X = Y);
      pragma Assert (Mod_To_Int (Int_To_Mod (X)) = X);
   end Test;
begin
   null;
end;
