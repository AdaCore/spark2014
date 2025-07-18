procedure Main with SPARK_Mode is
   type Int_Access is access Integer;
   type Int_Access_Constant is access constant Integer;

   type R is record
      F : Int_Access_Constant;
   end record;

   function F return R is
      X3 : Int_Access := new Integer'(12);
   begin
      return (F => Int_Access_Constant (X3));
   end F;

   function F_2 return R is
   begin
      return (F => new Integer'(12));
   end F_2;

   X1 : Int_Access := new Integer'(12);
   Y1 : R := (F => Int_Access_Constant (X1));
   X2 : Int_Access := new Integer'(12);
   Y2 : R;
   Y3 : R := (F => new Integer'(12));
   Y4 : R;
begin
   Y2 := (F => Int_Access_Constant (X2));
   Y2 := (F => new Integer'(12));
end Main;
