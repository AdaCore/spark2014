package Pack is

   protected type Prot is
      procedure P;
      entry E;
   private
      B : Boolean := False;
      X : Integer := 0;
   end Prot;

end Pack;
