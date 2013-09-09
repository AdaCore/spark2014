procedure Proc (A : in out Integer;
                B : in out Integer;
                C : in out Integer;
                D : in out Integer;
                E : in out Integer;
                F : in out Integer;
                G : in out Integer;
                H : in out Integer)
is
begin
   if A = 0 then
      A := A + 1;
   end if;
   pragma Assert_And_Cut (True);
   if B = 0 then
      B := B + 1;
   end if;
   pragma Assert_And_Cut (True);
   if C = 0 then
      C := C + 1;
   end if;
   pragma Assert_And_Cut (True);
   if D = 0 then
      D := D + 1;
   end if;
   pragma Assert_And_Cut (True);
   if E = 0 then
      E := E + 1;
   end if;
   pragma Assert_And_Cut (True);
   if F = 0 then
      F := F + 1;
   end if;
   pragma Assert_And_Cut (True);
   if G = 0 then
      G := G + 1;
   end if;
   pragma Assert_And_Cut (True);
   if H = 0 then
      H := H + 1;
   end if;
   pragma Assert_And_Cut (H = 0);
end Proc;
