package body Power_14.Source_A_14
is
   State : Integer;

   procedure Read (Level : out Integer)
   is
   begin
      Level := State;
   end Read;
end Power_14.Source_A_14;
