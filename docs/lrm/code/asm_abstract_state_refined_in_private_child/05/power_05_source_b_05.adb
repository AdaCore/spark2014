package body Power_05.Source_B_05
is
   State : Integer;

   procedure Read (Level : out Integer)
   is
   begin
      Level := State;
   end Read;
end Power_05.Source_B_05;
