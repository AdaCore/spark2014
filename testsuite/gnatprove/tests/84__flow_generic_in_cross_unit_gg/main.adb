with Inst;

with Ada.Real_Time; use Ada.Real_Time;

procedure Main is

   procedure Sub (R : out Time);
      --  with
      --       Global => null;           -- Wrong
      --       Global => Clock_Time;     -- Correct

   procedure Sub (R : out Time) is
   begin
      Inst.P (R);
   end;

   Q : Time;

begin
   Sub (Q);
end;
