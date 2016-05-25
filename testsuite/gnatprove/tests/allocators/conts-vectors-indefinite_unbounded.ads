------------------------------------------------------------------------------
--                     Copyright (C) 2015-2016, AdaCore                     --
--                                                                          --
-- This library is free software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License  as published by the Free --
-- Software  Foundation;  either version 3,  or (at your  option) any later --
-- version. This library is distributed in the hope that it will be useful, --
-- but WITHOUT ANY WARRANTY;  without even the implied warranty of MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE.                            --
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

--  Unbounded controlled vectors of unconstrained elements

pragma Ada_2012;
with Conts.Elements.Indefinite;
with Conts.Vectors.Generics;
with Conts.Vectors.Storage.Unbounded;

generic
   type Index_Type is (<>);
   type Element_Type (<>) is private;
   type Container_Base_Type is abstract tagged limited private;
   with procedure Free (E : in out Element_Type) is null;
package Conts.Vectors.Indefinite_Unbounded is

   package Elements is new Conts.Elements.Indefinite
      (Element_Type, Free => Free, Pool => Conts.Global_Pool);
   package Storage is new Conts.Vectors.Storage.Unbounded
      (Elements            => Elements.Traits,
       Container_Base_Type => Container_Base_Type,
       Resize_Policy       => Conts.Vectors.Resize_1_5);
   package Vectors is new Conts.Vectors.Generics (Index_Type, Storage.Traits);

   subtype Vector is Vectors.Vector;
   subtype Cursor is Vectors.Cursor;
   subtype Constant_Returned is Elements.Traits.Constant_Returned;

   package Cursors renames Vectors.Cursors;
   package Maps renames Vectors.Maps;

   function To_Index (Position : Cursor) return Index_Type
     renames Vectors.To_Index;
   procedure Swap
     (Self : in out Cursors.Forward.Container; Left, Right : Index_Type)
       renames Vectors.Swap;

end Conts.Vectors.Indefinite_Unbounded;
