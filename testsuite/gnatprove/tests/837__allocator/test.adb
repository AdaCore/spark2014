procedure Test with SPARK_Mode is
   type Int_Access is access Integer;

   type Int_Access_Constant is access constant Int_Access;

   type R is record
      F : Int_Access_Constant;
   end record;
   X1 : Int_Access := new Integer'(15);
   Y1 : R := (F => new Int_Access'(X1));
   pragma Assert (X1.all = 15);  --  Error, X1 is moved

begin
   null;
end;
