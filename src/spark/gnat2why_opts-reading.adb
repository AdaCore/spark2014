------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y _ O P T S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                Copyright (C) 2017-2020, Altran UK Limited                --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Call;          use Call;
with GNATCOLL.JSON; use GNATCOLL.JSON;

package body Gnat2Why_Opts.Reading is

   ----------
   -- Load --
   ----------

   procedure Load (Args_File : String; Source_File : String) is

      function Get_Opt
        (V     : JSON_Value;
         Field : String)
         return Boolean
      is
        (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the boolean value of the [Field] of the JSON record [V]

      function Get_Opt
        (V     : JSON_Value;
         Field : String)
         return Unbounded_String
      is
        (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the string value of the [Field] of the JSON record [V]

      procedure Read_File_Specific_Info (V : JSON_Value);

      -----------------------------
      -- Read_File_Specific_Info --
      -----------------------------

      procedure Read_File_Specific_Info (V : JSON_Value) is
         R : constant JSON_Value :=
           (if Has_Field (V, Source_File)
            then Get (V, Source_File)
            else Get (V, "Ada"));

      begin
         No_Loop_Unrolling := Get_Opt (R, No_Loop_Unrolling_Name);
         No_Inlining       := Get_Opt (R, No_Inlining_Name);
         Info_Messages     := Get_Opt (R, Info_Messages_Name);

         if not Global_Gen_Mode then
            Proof_Warnings := Get_Opt (R, Proof_Warnings_Name);

            declare
               Ar : constant JSON_Array := Get (R, Why3_Args_Name);
            begin
               for Var_Index in Positive range 1 .. Length (Ar) loop
                  Why3_Args.Append (Get (Get (Ar, Var_Index)));
               end loop;
            end;
         end if;
      end Read_File_Specific_Info;

      V : constant JSON_Value := Read_File_Into_JSON (Args_File);

   --  Start of processing for Load

   begin
      Global_Gen_Mode         := Get_Opt (V, Global_Gen_Mode_Name);
      Check_Mode              := Get_Opt (V, Check_Mode_Name);

      Debug_Mode              := Get_Opt (V, Debug_Mode_Name);
      Flow_Advanced_Debug     := Get_Opt (V, Flow_Advanced_Debug_Name);
      Flow_Generate_Contracts := Get_Opt (V, Flow_Generate_Contracts_Name);

      if not Global_Gen_Mode then
         Check_All_Mode     := Get_Opt (V, Check_All_Mode_Name);
         Flow_Analysis_Mode := Get_Opt (V, Flow_Analysis_Mode_Name);
         Prove_Mode         := Get_Opt (V, Prove_Mode_Name);

         Limit_Units  := Get_Opt (V, Limit_Units_Name);
         Limit_Subp   := Get_Opt (V, Limit_Subp_Name);
         Limit_Line   := Get_Opt (V, Limit_Line_Name);
         Limit_Region := Get_Opt (V, Limit_Region_Name);

         Output_Mode :=
           Output_Mode_Type'Value (Get (Get (V, Output_Mode_Name)));

         Report_Mode :=
           Report_Mode_Type'Value (Get (Get (V, Report_Mode_Name)));

         Warning_Mode :=
           SPARK_Warning_Mode_Type'Value (Get (Get (V, Warning_Mode_Name)));

         Pedantic               := Get_Opt (V, Pedantic_Name);
         Flow_Termination_Proof := Get_Opt (V, Flow_Termination_Name);
         Flow_Show_GG           := Get_Opt (V, Flow_Show_GG_Name);
         Proof_Generate_Guards  := Get_Opt (V, Proof_Generate_Guards_Name);
         Debug_Trivial          := Get_Opt (V, Debug_Trivial_Name);
         Ide_Mode               := Get_Opt (V, Ide_Mode_Name);
         CWE                    := Get_Opt (V, CWE_Name);

         Why3_Dir := Get_Opt (V, Why3_Dir_Name);

         if Has_Field (V, CP_Dir_Name) then
            CP_Res_Dir := Get_Opt (V, CP_Dir_Name);
         end if;
      end if;

      pragma Assert (Has_Field (V, File_Specific_Name));
      Read_File_Specific_Info (Get (V, File_Specific_Name));
   end Load;

end Gnat2Why_Opts.Reading;
