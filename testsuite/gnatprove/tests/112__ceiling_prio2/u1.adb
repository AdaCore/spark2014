with U2;

package body U1 is

   procedure P3;
   --  Private procedure without a contract. Likely to be inlined.

   procedure P3 is
   begin
      --  Body of a private procedure. Likely to be inlined.
      U2.P4;
   end;

   procedure P2 is
      --  Body of a public procedure.
   begin
      P3;
   end;

   procedure P1 is
      --  Body of a public procedure.
   begin
      P2;
   end;

   procedure PAA is
      --  Body of a public procedure.
   begin
      U2.PA;
   end;

end U1;
