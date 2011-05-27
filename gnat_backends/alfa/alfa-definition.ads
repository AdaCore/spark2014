------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                       A L F A . D E F I N I T I O N                      --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Sem_Util; use Sem_Util;

with Why.Inter; use Why.Inter;

package ALFA.Definition is

   type Unique_Entity_Id is new Entity_Id;
   --  Type of unique entities shared between different views, in contrast to
   --  GNAT entities which may be different between views in GNAT AST:
   --  * package spec and body have different entities;
   --  * subprogram declaration, subprogram stub and subprogram body all have
   --    a different entity;
   --  * private view and full view have a different entity.

   function Unique (E : Entity_Id) return Unique_Entity_Id is
      (Unique_Entity_Id (Unique_Entity (E)));

   type Violation_Kind is (V_Implem,           --  not yet implemented

                           V_Slice,            --  array slice
                           V_Container,        --  formal containers
                           V_Discr,            --  discriminant record
                           V_Dispatch,         --  dispatching
                           V_Block_Statement,  --  block declare statement
                           V_Generic,          --  generics
                           V_Impure_Function,  --  impure functions
                           V_Standard_Lib,     --  standard library
                           V_Tagged,           --  tagged type

                           V_Tasking,          --  tasks and protected objects
                           V_Other);           --  other violations of ALFA

   subtype V_Design is Violation_Kind range V_Slice .. V_Other;

   subtype V_Extensions is Violation_Kind range V_Slice .. V_Tagged;

   procedure Mark_Compilation_Unit (N : Node_Id);
   --  Put marks on a compilation unit. This should be called after all
   --  compilation units on which it depends have been marked.

   procedure Mark_Standard_Package;
   --  Put marks on package Standard

   function Standard_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;

   procedure Close_ALFA_Output_File;

   procedure Create_ALFA_Output_File (Filename : String);
   --  Create the file in which to generate output about subprogram in/out of
   --  the ALFA subset.

   type Alfa_Decl is
     (Alfa_Object,
      Alfa_Type,
      Non_Alfa_Object,  --  Entities, not declarations
      Non_Alfa_Type,    --  Entities, not declarations
      Alfa_Subprogram_Spec,
      Alfa_Subprogram_Body);

   type Alfa_Decls is array (Alfa_Decl) of List_Of_Nodes.List;

   Decls_In_Spec : Alfa_Decls;
   Decls_In_Body : Alfa_Decls;

end ALFA.Definition;
