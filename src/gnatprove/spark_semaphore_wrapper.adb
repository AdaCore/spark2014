------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--              S P A R K _ S E M A P H O R E _ W R A P P E R               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017-2025, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Command_Line; use Ada.Command_Line;
with Ada.Environment_Variables;
with Ada.Text_IO;
with GNAT.OS_Lib;      use GNAT.OS_Lib;
with Named_Semaphores; use Named_Semaphores;

procedure SPARK_Semaphore_Wrapper
  with No_Return
is

   --  This is a wrapper program, which runs the wrapped program only if the
   --  named semaphore is available for locking.

   --  The name of the semaphore is retrieved from the GNATPROVE_SEMAPHORE
   --  environment variable. If no such variable is set, the program returns an
   --  error.

   --  Invocation:
   --  spark_semaphore_wrapper command <args>

   Ret  : Integer;

   Args : String_List (1 .. Argument_Count - 1);
   --  Holds the arguments that will be passed to program to be spawned. We
   --  need one less than the arguments of the wrapper program, because we
   --  remove the name of the wrapper.

   Env_Var_Name : constant String := "GNATPROVE_SEMAPHORE";
begin
   if Argument_Count < 1 then
      Ada.Text_IO.Put_Line ("spark_semaphore_wrapper: not enough arguments");
      OS_Exit (1);
   end if;
   if not Ada.Environment_Variables.Exists (Env_Var_Name) then
      Ada.Text_IO.Put_Line
        ("spark_semaphore_wrapper: " & Env_Var_Name
         & "not set, semaphore name unknown");
      OS_Exit (1);
   end if;
   for I in Args'Range loop
      Args (I) := new String'(Argument (I + 1));
   end loop;
   declare
      Sem  : Semaphore;
      Prog : constant String_Access := Locate_Exec_On_Path (Argument (1));
   begin
      Open (Ada.Environment_Variables.Value (Env_Var_Name), Sem);
      Wait (Sem);
      Ret := Spawn (Prog.all, Args);
      Release (Sem);
      Close (Sem);
   end;
   OS_Exit (Ret);
end SPARK_Semaphore_Wrapper;
