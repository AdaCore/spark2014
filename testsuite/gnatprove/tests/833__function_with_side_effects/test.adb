procedure Test with SPARK_Mode is
   type Int_Access is access Integer;

   function F (X : in out Int_Access) return Int_Access with
     Side_Effects;

   function F (X : in out Int_Access) return Int_Access is
   begin
      return X;  --  Cannot exit with X moved
   end F;

   type Int_Access_Constant is access constant Int_Access;
   function F_2 (X : in out Int_Access) return Int_Access_Constant with
     Side_Effects;

   function F_2 (X : in out Int_Access) return Int_Access_Constant is
   begin
      return new Int_Access'(X);  --  Cannot exit with X moved
   end F_2;

begin
   null;
end;
