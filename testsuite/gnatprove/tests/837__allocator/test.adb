procedure Test with SPARK_Mode is
   type Int_Access is access Integer;

   type Int_Access_Constant is access constant Int_Access;

   type R is record
      F : Int_Access_Constant;
   end record;
   X1 : Int_Access := new Integer'(15);
   Y1 : R := (F => new Int_Access'(X1));
   pragma Assert (X1.all = 15);  --  Error, X1 is moved

   type RR is record
      G : Int_Access;
   end record;

   X2 : constant RR := (G => new Integer'(13));
   Y2 : Int_Access_Constant := new Int_Access'(X2.G);
   pragma Assert (X2.G.all = 13);  --  OK, G is a constant

   X3 : RR := (G => new Integer'(13));
   Y3 : Int_Access_Constant := new Int_Access'(X3.G);
   pragma Assert (X3.G.all = 13);  --  Error, X3 is moved

begin
   null;
end;
