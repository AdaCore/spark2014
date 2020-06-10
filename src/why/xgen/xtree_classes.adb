------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        X T R E E _ C L A S S E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

package body Xtree_Classes is

   ---------------------------------
   -- Print_Class_Case_Expression --
   ---------------------------------

   procedure Print_Class_Case_Expression
     (O            : in out Output_Record;
      CI           : Class_Info;
      Param        : String;
      Default      : String;
      Process_Kind : not null access procedure
                       (O    : in out Output_Record;
                        Kind : Why_Node_Kind);
      Case_Expr    : Boolean := True)
   is
      Sep : constant String := (if Case_Expr then "," else ";");
   begin
      if Case_Expr then
         P (O, "(");
      end if;

      PL (O, "case Get_Kind (" & Param & ") is");
      for Kind in Class_First (CI) .. Class_Last (CI) loop
         Relative_Indent (O, 3);
         PL (O, "when " & Mixed_Case_Name (Kind) & " =>");
         Relative_Indent (O, 3);
         Process_Kind (O, Kind);
         PL (O, Sep);
         Relative_Indent (O, -6);
      end loop;
      PL (O, "   when others =>");
      P  (O, "      " & Default);

      if Case_Expr then
         P (O, ");");
      else
         PL (O, ";");
         PL (O, "end case;");
      end if;
   end Print_Class_Case_Expression;

end Xtree_Classes;
