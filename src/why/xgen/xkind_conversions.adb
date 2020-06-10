------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    X K I N D _ C O N V E R S I O N S                     --
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

with Xkind_Tables; use Xkind_Tables;
with Why.Sinfo;    use Why.Sinfo;

package body Xkind_Conversions is

   Node_Id_Param : constant String := "Id";

   type Printed_Entities is (Decls, Bodies);
   --  Used to specify the kind of entity to print (declarations of bodies)

   procedure Print_Conversions
     (O : in out Output_Record;
      E : Printed_Entities);
   --  Same as Print_Conversion_Declarations/Print_Conversion_Bodies,
   --  depending on E.

   procedure Print_Conversion_Couple
     (O         : in out Output_Record;
      Id_Type   : String;
      Base_Type : String;
      E         : Printed_Entities);
   --  Print a couple of couversions from/to the given types

   procedure Print_Conversion
     (O    : in out Output_Record;
      From : String;
      To   : String;
      E    : Printed_Entities);
   --  Print a conversion from From to To. If E = Decls, print a declaration;
   --  otherwise, print parameterized expressions.

   procedure Print_Conversion_Spec
     (O    : in out Output_Record;
      From : String;
      To   : String);
   --  Print spec of conversion from From to To

   -----------------------
   -- Print_Conversions --
   -----------------------

   procedure Print_Conversions
     (O : in out Output_Record;
      E : Printed_Entities)
   is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Conversion_Declarations, but only for the kind
      --  pointed by Position.

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Conversion_Declarations, but only for the class
      --  pointed by Position.

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S      : constant String_Access :=
                    String_Lists.Element (Position);
         Prefix : constant String := S.all;
      begin
         for Multiplicity in Id_Lone .. Id_Set loop

            --  Conversion between a kind id and its base type

            Print_Conversion_Couple
              (O,
               Id_Subtype (Prefix, Derived, Multiplicity),
               Base_Id_Subtype (Prefix, Derived, Multiplicity),
               E);

            if Multiplicity /= Id_Set
              or else Position /= Kinds.Last
            then
               NL (O);
            end if;
         end loop;
      end Process_One_Node_Kind;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI1    : constant Class_Info := Class_Lists.Element (Position);
         Prefix : constant String := Class_Name (CI1);
         F1     : constant Why_Node_Kind := Class_First (CI1);
         L1     : constant Why_Node_Kind := Class_Last (CI1);
      begin
         for Multiplicity in Id_Lone .. Id_Set loop

            --  Conversion between a class id and its base type

            Print_Conversion_Couple
              (O,
               Id_Subtype (Prefix, Derived, Multiplicity),
               Base_Id_Subtype (Prefix, Derived, Multiplicity),
               E);

            --  Conversions between a class id and its elements

            for Kind in  F1 .. L1 loop
               NL (O);
               Print_Conversion_Couple
                 (O,
                  Id_Subtype (Prefix, Derived, Multiplicity),
                  Id_Subtype (Mixed_Case_Name (Kind), Derived, Multiplicity),
                  E);
            end loop;

            --  Conversions between a class id and the classes that
            --  strictly includes it.

            for CI2 of Classes loop
               if Is_Subclass (CI1, CI2) then
                  NL (O);
                  Print_Conversion_Couple
                    (O,
                     Id_Subtype (Prefix, Derived, Multiplicity),
                     Id_Subtype (Class_Name (CI2), Derived, Multiplicity),
                     E);
               end if;
            end loop;

            if Multiplicity /= Id_Set
              or else Position /= Classes.Last
            then
               NL (O);
            end if;
         end loop;
      end Process_One_Class_Kind;

   --  Start of processing for Print_Conversion_Declarations

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Conversions;

   -----------------------------
   -- Print_Conversion_Bodies --
   -----------------------------

   procedure Print_Conversion_Bodies (O : in out Output_Record) is
   begin
      Print_Conversions (O, Bodies);
   end Print_Conversion_Bodies;

   -----------------------------------
   -- Print_Conversion_Declarations --
   -----------------------------------

   procedure Print_Conversion_Declarations (O : in out Output_Record) is
   begin
      Print_Conversions (O, Decls);
   end Print_Conversion_Declarations;

   -----------------------------
   -- Print_Conversion_Couple --
   -----------------------------

   procedure Print_Conversion_Couple
     (O         : in out Output_Record;
      Id_Type   : String;
      Base_Type : String;
      E         : Printed_Entities) is
   begin
      Print_Conversion (O, Id_Type, Base_Type, E);
      NL (O);
      Print_Conversion (O, Base_Type, Id_Type, E);
   end Print_Conversion_Couple;

   ----------------------
   -- Print_Conversion --
   ----------------------

   procedure Print_Conversion
     (O    : in out Output_Record;
      From : String;
      To   : String;
      E    : Printed_Entities)
   is
   begin
      Print_Conversion_Spec (O, From, To);

      if E = Decls then
         PL (O, ";");
      else
         PL (O, " is");
         PL (O, "  (" & To & " (" & Node_Id_Param & "));");
      end if;
   end Print_Conversion;

   ---------------------------
   -- Print_Conversion_Spec --
   ---------------------------

   procedure Print_Conversion_Spec
     (O    : in out Output_Record;
      From : String;
      To   : String)
   is
   begin
      PL (O, "function ""+""");
      PL (O, "  (" & Node_Id_Param & " : " & From & ")");
      P  (O, "  return " & To);
   end Print_Conversion_Spec;

end Xkind_Conversions;
