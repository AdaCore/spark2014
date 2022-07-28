with Q; use Q;

with Ada.Text_IO;  use Ada.Text_IO;

procedure Demo_Problem with SPARK_Mode is

   S : Set := Null_Set;

   procedure Print (Prompt : String;  This : Set) is
   begin
      Put (Prompt & """");
      for C : Contained_Element of This loop
         Put (C);
      end loop;
      Put_Line ("""");
   end Print;

begin
   Print ("S contains ", S);

   Put_Line ("Done");
end Demo_Problem;
