with Except;
with Screen_Output; use Screen_Output;
with Stack;
with Tokens; use Tokens;
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line; with Set_Input_File;

procedure Sdc
with SPARK_Mode => On
is
   File : File_Type;
   T : Token;
begin
   Msg ("Welcome to sdc. Go ahead type your commands ...");

   if Argument_Count = 1 then
      Open (File, In_File, Argument (1));
      Set_Input_File (File);
   end if;

   loop
      Next (T);
      Process (T);
      --  Read the next Token from the input and process it.
   end loop;
end Sdc;
