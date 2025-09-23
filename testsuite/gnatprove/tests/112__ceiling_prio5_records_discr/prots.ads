package Prots is

   protected type PT (Ceiling : Positive) is
      pragma Priority (Ceiling);

      procedure PP1
      with Global => null, Always_Terminates;
   end;

   subtype PT1 is PT (1);
   subtype PT2 is PT (2);

   PO1 : PT (1);
   PO2 : PT (2);

   type R is record
      F1 : PT1;
      F2 : PT2;
   end record;

   Obj1 : R;
   Obj2 : R;

end Prots;
