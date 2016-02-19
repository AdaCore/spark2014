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

   procedure Match (Self : Pattern_Matcher)
   is
      Short_Program : Program_Data renames Self.Program; -- Shorter notation
   begin
      pragma Assert (Short_Program (1) /= BRANCH);
   end Match;

end Regpat;
