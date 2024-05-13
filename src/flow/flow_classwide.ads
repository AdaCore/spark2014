------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       F L O W _ C L A S S W I D E                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--              Copyright (C) 2015-2024, Capgemini Engineering              --
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
------------------------------------------------------------------------------

--  This package deals with the sanity checking of classwide flow contracts

with Atree;          use Atree;
with Einfo.Entities; use Einfo.Entities;
with Sinfo.Nodes;    use Sinfo.Nodes;
with Types;          use Types;

package Flow_Classwide is

   function Is_Dispatching_Call (N : Node_Id) return Boolean
   is (Nkind (N) in N_Subprogram_Call
       and then Present (Controlling_Argument (N)))
   with Pre => Nkind (N) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  Checks if the given call node is dispatching

   procedure Check_Classwide_Contracts (E : Entity_Id)
   with Pre => Nkind (E) in N_Entity and then
               Ekind (E) in E_Function | E_Procedure;
   --  Checks the classwide contracts of the given subprogram and if not valid
   --  then some error messages will have been issued. If the subprogram does
   --  not have a controlling parameter nor a result, this check procedure does
   --  nothing.

end Flow_Classwide;
