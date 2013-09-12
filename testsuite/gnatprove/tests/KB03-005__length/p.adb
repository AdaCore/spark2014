procedure P is 
   type Vec is array (Integer range <>) of Integer;
   subtype Vec_10_Sub is Vec (0 .. 10);

   procedure Nothing  (X : Vec_10_Sub) is
   begin
      null;
   end Nothing;

   function F return Integer is
   begin
      return 1;
   end F;

   A : Vec (F .. 10);
begin
   Nothing (A);
end P;
