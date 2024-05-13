package body P is

   procedure P is
      Tmp : Integer;
   begin
      Tmp := V;
   end P;

   function F return Integer is
   begin
      return V;
   end F;

   procedure P2 is
      Tmp : Integer;
   begin
      Tmp := V2;
   end P2;

   function F2 return Integer is
   begin
      return V2;
   end F2;

end P;
