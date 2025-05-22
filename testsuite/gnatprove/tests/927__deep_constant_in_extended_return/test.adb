procedure Test with Spark_Mode is

   type Int_Acc is access Integer;

   type C_Int_Acc is access constant Integer;

   type R is record
      F : Int_Acc;
   end record;

   V : C_Int_Acc;

   --  F creates an alias between its result and C. It should be rejected or
   --  the incorrect assertion in Bad_Use_F would be proved.

   function F return R with
     Side_Effects,
     Post => V /= null and F'Result.F /= null;

   function F return R is
   begin
      return G : constant R := (F => new Integer'(12)) do
         V := C_Int_Acc (G.F);
      end return;
   end F;

   procedure Bad_Use_F is
      W : R;
      I : Integer;
   begin
      W := F;
      I := V.all;
      W.F.all := 0;
      pragma Assert (I = V.all); --  This assertion fails at runtime
   end Bad_Use_F;

begin
   Bad_Use_F;
end;
