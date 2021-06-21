with Ada.Unchecked_Conversion;

procedure Deep_Overlay with SPARK_Mode is
   type Int_Access is access Integer;

   function F is new Ada.Unchecked_Conversion (Int_Access, Long_Long_Integer);
   function G is new Ada.Unchecked_Conversion (Long_Long_Integer, Int_Access);

   X : Int_Access;
   Y : Long_Long_Integer with Import,
     Address => X'Address;
   W : Long_Long_Integer := 0;
   Z : Int_Access with
     Import,
     Address => W'Address;
begin
   null;
end Deep_Overlay;
