procedure P is
   type Vec is array (Integer range <>) of Integer;
   subtype Vec_10_Sub is Vec (0 .. 10);

   procedure Init (X : out Vec) is
   begin
      X := (others => 1);
   end Init;

   function F return Integer is
   begin
      return 1;
   end F;

   A : Vec (F .. 10);
begin
   Init (A);
end P;
