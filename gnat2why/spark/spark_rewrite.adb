------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S P A R K _ R E W R I T E                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                        Copyright (C) 2013, AdaCore                       --
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

with Atree;   use Atree;
with Einfo;   use Einfo;
with Sem_Aux; use Sem_Aux;
with Sinfo;   use Sinfo;

package body SPARK_Rewrite is

   procedure Rewrite_Call (N : Node_Id);
   --  Replace renamings and inherited subprograms by the subprogram they
   --  rename or inherit.

   ------------------
   -- Rewrite_Call --
   ------------------

   procedure Rewrite_Call (N : Node_Id) is
   begin
      --  If the subprogram is a renaming or an inherited primitive operation,
      --  replace it in the call with the name of the actual subprogram being
      --  called. Both have an Alias component, that points to the immediate
      --  renamed or inherited subprogram. The Ultimate_Alias function
      --  retrieves the last subprogram in a chain of aliases. Note that
      --  renamings and inherited primitive operations can be distinguished
      --  by the kind of their parent node: the entity for a renaming has
      --  the function or procedure specification node as parent, while an
      --  inherited primitive operation has the derived type declaration as
      --  parent.

      if Nkind (Name (N)) in N_Has_Entity
        and then Present (Entity (Name (N)))
      then
         declare
            E : constant Entity_Id := Entity (Name (N));
         begin
            if (Is_Overloadable (E) or else Ekind (E) = E_Subprogram_Type)
              and then Present (Alias (E))
            then
               Set_Entity (Name (N), Ultimate_Alias (E));
            end if;
         end;
      end if;
   end Rewrite_Call;

   ------------------------------
   -- Rewrite_Compilation_Unit --
   ------------------------------

   procedure Rewrite_Compilation_Unit (N : Node_Id) is

      function Rewrite_Node (N : Node_Id) return Traverse_Result;
      --  Apply expansion operations on a node

      ------------------
      -- Rewrite_Node --
      ------------------

      function Rewrite_Node (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Subprogram_Call =>
               Rewrite_Call (N);
            when others =>
               null;
         end case;
         return OK;
      end Rewrite_Node;

      procedure Rewrite_Nodes is
        new Traverse_Proc (Rewrite_Node);

   begin
      Rewrite_Nodes (N);
   end Rewrite_Compilation_Unit;

end SPARK_Rewrite;
