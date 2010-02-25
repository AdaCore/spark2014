------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--            S P A R K I F Y . S O U R C E _ T R A V E R S A L             --
--                                                                          --
--                                 S p e c                                  --
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

--  This package defines the main traversal engine for Sparkify

with Asis;
with Asis.Iterator;                    use Asis.Iterator;

with Sparkify.Common;                  use Sparkify.Common;

package Sparkify.Source_Traversal is

   procedure Pre_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Source_Traversal_State);
   --  Pre-operation for traversal. The general idea is to perform the start of
   --  a special printing of the Element being visited. See the body for more
   --  information.

   procedure Post_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Source_Traversal_State);
   --  Post-operation for traversal. The general idea is to complete the
   --  special printing of the Element being visited. See the body for more
   --  information.

   procedure Traverse_Source is new Traverse_Element
     (State_Information => Source_Traversal_State);

end Sparkify.Source_Traversal;
