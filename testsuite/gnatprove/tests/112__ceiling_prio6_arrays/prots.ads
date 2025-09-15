package Prots is
   pragma Warnings(Off, "subprogram * has no effect");

   protected type PT with Priority => 3 is
      procedure PP1
      with Global => null, Always_Terminates;
      procedure PP2
      with Global => null, Always_Terminates;
   end;

   procedure Proc1;
   procedure Proc2;
   procedure Proc3;
   procedure Flip;

end Prots;
