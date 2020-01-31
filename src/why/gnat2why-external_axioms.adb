------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y - E X T E R N A L _ A X I O M S             --
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

with Common_Containers;   use Common_Containers;
with GNATCOLL.Symbols;    use GNATCOLL.Symbols;
with Gnat2Why.Util;       use Gnat2Why.Util;
with Nlists;              use Nlists;
with SPARK_Util;          use SPARK_Util;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Gen.Arrays;      use Why.Gen.Arrays;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Images;          use Why.Images;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

package body Gnat2Why.External_Axioms is

   EA_Symbols : Symbol_Sets.Set;

   procedure Register_External_Entities (Package_Entity : Entity_Id);
   --  This function is called on a package with external axioms.
   --  It registers all entities in the global symbol table.

   ------------------------------
   -- Is_External_Axiom_Module --
   ------------------------------

   function Is_External_Axiom_Module (Module : W_Module_Id) return Boolean is
   begin
      return EA_Symbols.Contains (Get_Name (Module));
   end Is_External_Axiom_Module;

   -------------------------------
   -- Process_External_Entities --
   -------------------------------

   procedure Process_External_Entities
     (Package_Entity : Entity_Id;
      Process        : not null access procedure (E : Entity_Id))
   is

      procedure Process_Decls (Decls : List_Id);
      --  Process entities from the declaration list

      -------------------
      -- Process_Decls --
      -------------------

      procedure Process_Decls (Decls : List_Id) is
         N : Node_Id := First (Decls);

      begin
         --  For object, subprogram, and type declarations call Process on the
         --  defining entity.

         while Present (N) loop

            --  A subprogram may have been rewritten by the frontend, in
            --  particular, it happens for expression functions. In this case,
            --  the declaration won't come from source but its original node
            --  will.

            if Comes_From_Source (Original_Node (N)) then
               case Nkind (N) is
                  when N_Full_Type_Declaration
                     | N_Private_Extension_Declaration
                     | N_Private_Type_Declaration
                     | N_Subtype_Declaration
                     | N_Object_Declaration
                  =>
                     Process (Defining_Identifier (N));

                  when N_Subprogram_Declaration =>
                     Process (Unique_Defining_Entity (N));

                  --  Call Process_Decls recursively on Package_Declaration and
                  --  Package_Instantiation.

                  when N_Package_Declaration =>
                     Process_Decls
                       (Decls => Visible_Declarations_Of_Package
                          (Unique_Defining_Entity (N)));

                  when others =>
                     null;
               end case;
            end if;

            Next (N);
         end loop;
      end Process_Decls;

   --  Start of processing for Process_External_Entities

   begin
      --  Process declarations

      Process_Decls
        (Decls => Visible_Declarations_Of_Package (Package_Entity));
   end Process_External_Entities;

   --------------------------------
   -- Register_External_Entities --
   --------------------------------

   procedure Register_External_Entities (Package_Entity : Entity_Id) is

      procedure Register_Entity (E : Entity_Id) with
        Pre => Ekind (E) /= E_Operator;
      --  Register entities declared in a package with external axioms in the
      --  symbol table. Also clones array theories for these entities if
      --  necessary.

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
                       Mutable  => False,
                       Labels   => <>));

      ---------------------
      -- Register_Entity --
      ---------------------

      procedure Register_Entity (E : Entity_Id) is
      begin

         --  Store symbols for subprogram and object entities in the symbol
         --  table so they can be retrieved when translating user code.

         if Ekind (E) in Subprogram_Kind | Object_Kind then
            if Ekind (E) = E_Function then
               declare
                  Name       : constant String := Short_Name (E);
                  Logic_Name : constant String := Name & "__logic";
               begin
                  Ada_Ent_To_Why.Insert
                    (Symbol_Table, E,
                     Item_Type'(Func,
                       Local     => False,
                       Init      => <>,
                       For_Logic => Get_Subp_Symbol (E, Logic_Name),
                       For_Prog  => Get_Subp_Symbol (E, Name)));
               end;
            elsif Ekind (E) = E_Procedure then
               Insert_Entity
                 (E,
                  To_Why_Id (E, Domain => EW_Term),
                  Mutable => False);
            else
               pragma Assert (Is_Object (E));
               Ada_Ent_To_Why.Insert
                 (Symbol_Table, E, Mk_Item_Of_Entity (E));
            end if;
         end if;

         --  If there is a user declaration of an array type, possibly
         --  create a new type of array by cloning underlying Why3 theories.
         --  If the type of the array's component is declared locally to the
         --  package with external axioms, it is the responsability of the
         --  theory file to provide the new array type.

         if Is_Array_Type (E) then
            declare
               File             : constant W_Section_Id := Dispatch_Entity (E);
               Element_Is_Local : constant Boolean :=
                 Containing_Package_With_Ext_Axioms (Component_Type (E)) =
                   Package_Entity;
               S                : constant Symbol := Get_Array_Theory_Name (E);
               M                : constant W_Module_Id :=
                 New_Module (File => No_Symbol, Name => Img (S));
            begin
               Create_Rep_Array_Theory_If_Needed
                 (File          => File,
                  E             => E,
                  Register_Only => Element_Is_Local);
               EA_Symbols.Insert (Get_Name (M));
            end;
         end if;

         --  Register the module belonging to the entity E as being declared in
         --  a package with External Axioms.

         EA_Symbols.Insert (Get_Name (E_Module (E)));
         EA_Symbols.Insert (Get_Name (E_Rep_Module (E)));
         EA_Symbols.Insert (Get_Name (E_Compl_Module (E)));
         EA_Symbols.Insert (Get_Name (E_Init_Module (E)));
      end Register_Entity;

   --  Start of processing for Register_External_Entities

   begin
      Process_External_Entities (Package_Entity, Register_Entity'Access);
   end Register_External_Entities;

   --------------------------------------------
   -- Translate_Package_With_External_Axioms --
   --------------------------------------------

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id)
   is
      TFile : Why_Section renames
              Why_Sections (Dispatch_Entity (Package_Entity));

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
