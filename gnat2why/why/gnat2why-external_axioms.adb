------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y - E X T E R N A L _ A X I O M S             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Ada.Containers.Doubly_Linked_Lists;
with Atree;                              use Atree;
with Common_Containers;                  use Common_Containers;
with Einfo;                              use Einfo;
with Exp_Util;                           use Exp_Util;
with Gnat2Why.Util;                      use Gnat2Why.Util;
with Namet;                              use Namet;
with Nlists;                             use Nlists;
with Sem_Aux;                            use Sem_Aux;
with Sem_Util;                           use Sem_Util;
with Sinfo;                              use Sinfo;
with SPARK_Util;                         use SPARK_Util;
with Why.Atree.Builders;                 use Why.Atree.Builders;
with Why.Atree.Modules;                  use Why.Atree.Modules;
with Why.Gen.Arrays;                     use Why.Gen.Arrays;
with Why.Gen.Binders;                    use Why.Gen.Binders;
with Why.Gen.Names;                      use Why.Gen.Names;
with Why.Ids;                            use Why.Ids;
with Why.Inter;                          use Why.Inter;
with Why.Sinfo;                          use Why.Sinfo;
with Why.Types;                          use Why.Types;

package body Gnat2Why.External_Axioms is

   package List_Of_Entity is new
     Ada.Containers.Doubly_Linked_Lists (Entity_Id);

   procedure Register_External_Entities (E : Entity_Id);
   --  This function is called on a package with external axioms.
   --  It registers all entities in the global symbol table.

   --------------------------------
   -- Register_External_Entities --
   --------------------------------

   procedure Register_External_Entities (E : Entity_Id) is

      procedure Register_Decls (Decls : List_Id);
      --  Register the entities of the declarations

      function Get_Subp_Symbol
        (E    : Entity_Id;
         Name : String) return Binder_Type
      is
         (Binder_Type'(B_Name   => New_Identifier
                         (Ada_Node => E,
                          Name     => Name,
                          Module   => E_Module (E),
                          Typ      => Type_Of_Node (Etype (E))),
                       B_Ent    => Null_Entity_Name,
                       Ada_Node => E,
                       Mutable  => False));

      --------------------
      -- Register_Decls --
      --------------------

      procedure Register_Decls (Decls : List_Id) is
         N : Node_Id := First (Decls);
      begin
         while Present (N) loop

            --  A subprogram may have been rewritten by the frontend, in
            --  particular, it happens for expression functions. In this case,
            --  the declaration won't come from source but its original node
            --  will.

            if (Comes_From_Source (N)
                or else (Present (Original_Node (N))
                         and then Comes_From_Source (Original_Node (N))))
              and then Nkind (N) in N_Subprogram_Declaration
              | N_Object_Declaration
            then
               declare
                  E : constant Entity_Id := Defining_Entity (N);
                  Name : constant String := Short_Name (E);
                  Logic_Name : constant String :=
                    Name & "__logic";
               begin
                  if Ekind (E) = E_Function then
                     Ada_Ent_To_Why.Insert
                       (Symbol_Table, E,
                        Item_Type'(Func,
                          For_Logic => Get_Subp_Symbol (E, Logic_Name),
                          For_Prog  => Get_Subp_Symbol (E, Name)));
                  elsif Ekind (E) = E_Procedure then
                     Insert_Entity
                       (E,
                        To_Why_Id (E, Domain => EW_Term),
                        Mutable => False);
                  else
                     Ada_Ent_To_Why.Insert
                       (Symbol_Table, E, Mk_Item_Of_Entity (E));
                  end if;
               end;
            end if;

            --  If there is a user declaration of an array type, possibly
            --  create a new type of array by cloning underlying Why3 theories.
            --  If the type of the array's component is declared locally to the
            --  package with external axioms, it is the responsability of the
            --  theory file to provide the new array type.

            if Comes_From_Source (N)
              and then Nkind (N) = N_Full_Type_Declaration
              and then Is_Array_Type (Defining_Identifier (N))
            then
               declare
                  File : constant W_Section_Id :=
                    Dispatch_Entity (Defining_Identifier (N));
                  Element_Is_Local : constant Boolean :=
                    Containing_Package_With_Ext_Axioms
                      (Component_Type (Defining_Identifier (N))) = E;
               begin
                  Create_Rep_Array_Theory_If_Needed
                    (File          => File,
                     E             => Defining_Identifier (N),
                     Register_Only => Element_Is_Local);
               end;
            end if;

            --  Call Register_Decls recursively on Package_Declaration and
            --  Package_Instantiation.

            if Comes_From_Source (N) and then
              Nkind (N) = N_Package_Instantiation
            then
               Register_Decls
                 (Decls  => Visible_Declarations
                    (Specification (Instance_Spec (N))));
            end if;

            if Comes_From_Source (N) and then
              Nkind (N) in N_Package_Declaration
            then
               Register_Decls
                 (Decls  => Visible_Declarations (Package_Specification (N)));
            end if;

            Next (N);
         end loop;
      end Register_Decls;

   --  Start of processing for Register_External_Entities

   begin
      Register_Decls
        (Decls  => Visible_Declarations (Package_Specification (E)));
   end Register_External_Entities;

   --------------------------------------------
   -- Translate_Package_With_External_Axioms --
   --------------------------------------------

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id)
   is

      TFile : Why_Section renames
              Why_Sections (Dispatch_Entity (Package_Entity));

   --  Start of processing for Translate_Package_With_External_Axioms

   begin
      Register_External_Entities (Package_Entity);

      declare
         Decl : constant W_Custom_Declaration_Id :=
                  New_Custom_Declaration
                    (Ada_Node  => Package_Entity,
                     Domain    => EW_Prog,
                     File_Name => NID (Full_Name (Package_Entity) & ".mlw"));
      begin
         TFile.Theories.Append (Why_Node_Id (Decl));
      end;
   end Translate_Package_With_External_Axioms;

end Gnat2Why.External_Axioms;
