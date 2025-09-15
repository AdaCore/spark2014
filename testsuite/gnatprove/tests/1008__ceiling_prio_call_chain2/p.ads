package P is

   procedure Q2;

private

   protected type PT with Priority => 1 is
      procedure PP1
      with Global => null, Always_Terminates;

      procedure PP2
      with Global => null, Always_Terminates;
   end;

   PO1 : PT;
   PO2 : PT;

end P;
