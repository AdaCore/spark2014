package body Stacks is

   procedure Push (Top : in out IntMax; Data : in out Elements; E : Integer) is
   begin
      Top := Top + 1;
      Data (Top) := E;
   end Push;

   procedure Pop (Top : in out IntMax; Data : in out Elements) is
   begin
      Top := Top - 1;
   end Pop;

end Stacks;
