package body Power_05.Source_A_05
--# own State is S;
is
   S : Integer := 0;

   procedure Read (Level : out Integer)
   --# global in S;
   --# derives Level from S;
   is
   begin
      Level := S;
   end Read;
end Power_05.Source_A_05;
