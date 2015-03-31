package body Power_05.Source_B_05
--# own State is S;
is
   S : Integer := 0;

   procedure Read (Level : out Integer)
   --# global S;
   --# derives Level from S;
   is
   begin
      Level := S;
   end Read;
end Power_05.Source_B_05;
