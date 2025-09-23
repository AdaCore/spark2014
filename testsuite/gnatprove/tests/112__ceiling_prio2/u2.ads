package U2 is

   protected PO
     with Priority => 3
   is
      procedure PP1
      with Global => null, Always_Terminates;
   end;

   procedure P4;
   --  Public procedure. Not inlined.

   procedure P5;
   --  Public procedure. Not inlined.

   procedure PA;
   --  Public procedure. Not inlined.

end U2;
