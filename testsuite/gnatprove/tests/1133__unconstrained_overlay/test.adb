procedure Test with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;

   function G (X : Int_Array) return Integer with
     Pre => X'Length = 1
   is
      C : constant Integer with Import, Address => X'Address;
   begin
      return C;
   end G;

   function G_2 (X : Int_Array) return Integer is
      C : constant Integer with Import, Address => X'Address;
   begin
      return C;
   end G_2;

   type Cst_Acc is not null access constant Int_Array;

   function F (X : Cst_Acc) return Integer with
     Pre => X'Length = 1
   is
      C : constant Integer with Import, Address => X.all'Address;
   begin
      return C;
   end F;

   function F_2 (X : Cst_Acc) return Integer is
      C : constant Integer with Import, Address => X.all'Address;
   begin
      return C;
   end F_2;

begin
   null;
end;
