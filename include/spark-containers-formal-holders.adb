------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                     SPARK.CONTAINERS.FORMAL.HOLDERS                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2022-2023, Free Software Foundation, Inc.         --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Unchecked_Deallocation;

package body SPARK.Containers.Formal.Holders is

   procedure Finalize_Element is new Ada.Unchecked_Deallocation
     (Object => Element_Type,
      Name   => Element_Type_Access);
   --  Deallocate an Element_Type

   ------------
   -- Adjust --
   ------------

   procedure Adjust (Source : in out Holder_Type) is
   begin
      if Source.Element /= null then
         Source.Element := new Element_Type'(Source.Element.all);
      end if;
   end Adjust;

   -------------
   -- Element --
   -------------

   function Element (Container : Holder_Type) return Element_Type is
   begin
      if Container.Element = null then
         raise Constraint_Error with "Holder is empty";
      end if;

      return Container.Element.all;
   end Element;

   --------------------
   -- Element_Access --
   --------------------

   function Element_Access
     (Container : Holder_Type) return not null access Element_Type
   is
   begin
      if Container.Element = null then
         raise Constraint_Error with "Holder is empty";
      end if;

      return Container.Element;
   end Element_Access;

   --------------
   -- Finalize --
   --------------

   procedure Finalize (Container : in out Holder_Type) is
   begin
      if Container.Element /= null then
         Finalize_Element (Container.Element);
      end if;
   end Finalize;

   ----------
   -- Move --
   ----------

   procedure Move (Target, Source : in out Holder_Type) is
   begin
      if Target.Element /= null then
         Finalize_Element (Target.Element);
      end if;

      Target.Element := Source.Element;
      Source.Element := null;
   end Move;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (Container : in out Holder_Type;
      Element   : Element_Type)
   is
   begin
      if Container.Element /= null then
         Finalize_Element (Container.Element);
      end if;

      Container.Element := new Element_Type'(Element);
   end Replace_Element;

end SPARK.Containers.Formal.Holders;
