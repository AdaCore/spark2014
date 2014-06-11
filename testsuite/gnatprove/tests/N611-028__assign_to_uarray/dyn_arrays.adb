package body Dyn_Arrays with SPARK_Mode is

   procedure Copy_Bad (From : Nat_Array_Max; To : out Nat_Array) is
   begin
      To := From;
   end Copy_Bad;

   procedure Copy (From : Nat_Array_Max; To : out Nat_Array) is
   begin
      To := From;
   end Copy;

end;
