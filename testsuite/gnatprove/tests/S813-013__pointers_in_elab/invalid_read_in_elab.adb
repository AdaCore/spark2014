procedure Invalid_Read_In_Elab with SPARK_Mode is
   type Int_Acc is access Integer;

   X : Int_Acc := new Integer'(34);

   package Nested is
      Z1 : Integer := X.all;
      procedure P;
   end Nested;

   Y : Int_Acc := X;

   package body Nested is
      procedure P is null;

      Z2 : Integer := X.all;
   end Nested;

   package Nested_2 is
      Z1 : Integer := X.all;
   end Nested_2;

   V : Int_Acc := new Integer'(34);

   package Nested_B is
      Z1 : Integer := V.all;
      procedure P;
   end Nested_B;

   W : access Integer := V;

   package body Nested_B is
      procedure P is null;

      Z2 : Integer := V.all;
   end Nested_B;

   package Nested_B_2 is
      Z1 : Integer := V.all;
   end Nested_B_2;
begin
   null;
end Invalid_Read_In_Elab;
