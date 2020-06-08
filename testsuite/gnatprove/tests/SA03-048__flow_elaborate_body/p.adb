package body P is
   procedure Set (A : out Boolean) is
   begin
      A := True;
   end Set;
begin
   Set (X);
   Set (Y.C);
end P;
