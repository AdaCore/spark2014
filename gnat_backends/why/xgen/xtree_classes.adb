------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        X T R E E _ C L A S S E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
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
      Param        : Wide_String;
      Default      : Wide_String;
      Process_Kind : not null access procedure
                       (O    : in out Output_Record;
                        Kind : Why_Node_Kind))
   is
   begin
      PL (O, "(case Get_Kind (" & Param & ") is");
      for Kind in Class_First (CI) .. Class_Last (CI) loop
         Relative_Indent (O, 3);
         PL (O, "when " & Mixed_Case_Name (Kind) & " =>");
         Relative_Indent (O, 3);
         Process_Kind (O, Kind);
         PL (O, ",");
         Relative_Indent (O, -6);
      end loop;
      PL (O, "   when others =>");
      P  (O, "      " & Default & ");");
   end Print_Class_Case_Expression;

end Xtree_Classes;
