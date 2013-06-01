package Body Pre is

   function Pred (X : I) return Boolean is
      type Non_Alfa is access Integer;
   begin
      return True;
   end Pred;

   procedure P (Z : I) is
   begin
      pragma Assert (Pred (Z));
   end P;
end Pre;
