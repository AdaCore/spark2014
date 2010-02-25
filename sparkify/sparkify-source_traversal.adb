------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--            S P A R K I F Y . S O U R C E _ T R A V E R S A L             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Wide_Text_IO;                 use Ada.Wide_Text_IO;

with Asis.Elements;                    use Asis.Elements;
with Asis.Extensions.Flat_Kinds;       use Asis.Extensions.Flat_Kinds;
with ASIS_UL.Common;                   use ASIS_UL.Common;

with Sparkify.Pre_Operations;          use Sparkify.Pre_Operations;
with Sparkify.Post_Operations;         use Sparkify.Post_Operations;

package body Sparkify.Source_Traversal is

   -------------------
   -- Pre_Operation --
   -------------------

   procedure Pre_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      Arg_Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin

      --  Element_Kind-specific processing
      Specific_Pre_Operation (Arg_Kind) (Element, Control, State);

   exception
      when others =>
         Put (Standard_Error, "Pre_Operation failed for");
         New_Line (Standard_Error);
         Put (Standard_Error, Debug_Image (Element));
         New_Line (Standard_Error);

         raise; --  Fatal_Error;
   end Pre_Operation;

   --------------------
   -- Post_Operation --
   --------------------

   procedure Post_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      Arg_Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin

      --  Element_Kind-specific processing
      Specific_Post_Operation (Arg_Kind) (Element, Control, State);

   exception
      when others =>
         Put (Standard_Error, "Post_Operation failed for");
         New_Line (Standard_Error);
         Put (Standard_Error, Debug_Image (Element));
         New_Line (Standard_Error);

         raise Fatal_Error;
   end Post_Operation;

end Sparkify.Source_Traversal;
