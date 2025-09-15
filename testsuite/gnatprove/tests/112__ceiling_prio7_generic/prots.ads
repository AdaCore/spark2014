package Prots is

   procedure P1;
   --  Priority of the caller must be <= 3

   procedure P2;
   --  Priority of the caller must be <= 3

   procedure P3;
   --  Priority of the caller must be <= 3

private

   generic
      Prio : Integer;
   package Gen is

      protected PO
        with Priority => Prio

      is
         procedure PP1
         with Global => null, Always_Terminates;
      end;
   end;

end Prots;
