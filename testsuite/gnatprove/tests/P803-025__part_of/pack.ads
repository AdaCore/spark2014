package Pack is

   protected Prot is
      procedure P;
   private
      B : Boolean := False;
   end Prot;

   X : Integer := 0 with Part_Of => Prot;
end Pack;
