package body Regpat is

   type Opcode is (BRANCH);

   ---------
   -- "=" --
   ---------

   function "=" (Left : Character; Right : Opcode) return Boolean is
   begin
      return Character'Pos (Left) = Opcode'Pos (Right);
   end "=";

   -----------
   -- Match --
   -----------

   procedure Match
   is
      Left  : Character := ASCII.NUL;
      Right : Opcode    := BRANCH;
   begin
      pragma Assert (not (Left /= Right));
   end Match;

end Regpat;
