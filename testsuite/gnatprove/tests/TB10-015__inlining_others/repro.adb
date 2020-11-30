procedure Repro is

   type S is array (1 .. 5) of Integer;

   function Ident (X : Integer) return Integer is (X);

   procedure Check (X : S) is
   begin
      pragma Assert (X'Length = Ident (5));
   end Check;

begin
   Check ((others => 1));
end Repro;
