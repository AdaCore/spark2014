package body Power_05.Source_A_05
is
   State : Integer;

   procedure Read (Level : out Integer)
   is
   begin
      Level := State;
   end Read;
end Power_05.Source_A_05;
