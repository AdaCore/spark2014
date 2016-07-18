-- This smart pointers implementation originates from Booch Components
-- and it has the following copyright notice:
--
--  Copyright 1998-2003 Simon Wright <simon@pushface.org>
--
--  This package is free software; you can redistribute it and/or
--  modify it under terms of the GNU General Public License as
--  published by the Free Software Foundation; either version 2, or
--  (at your option) any later version. This package is distributed in
--  the hope that it will be useful, but WITHOUT ANY WARRANTY; without
--  even the implied warranty of MERCHANTABILITY or FITNESS FOR A
--  PARTICULAR PURPOSE. See the GNU General Public License for more
--  details. You should have received a copy of the GNU General Public
--  License distributed with this package; see file COPYING.  If not,
--  write to the Free Software Foundation, 59 Temple Place - Suite
--  330, Boston, MA 02111-1307, USA.
--
--  As a special exception, if other files instantiate generics from
--  this unit, or you link this unit with other files to produce an
--  executable, this unit does not by itself cause the resulting
--  executable to be covered by the GNU General Public License.  This
--  exception does not however invalidate any other reasons why the
--  executable file might be covered by the GNU Public License.
--
--  $Revision: 1420 $
--  $Date: 2009-09-26 18:42:21 +0100 (Sat, 26 Sep 2009) $
--  $Author: simonjwright $

private with Ada.Finalization;

generic
   type T (<>) is limited private;
   type P is access T;
package Aida.Generic_Shared_Ptr with SPARK_Mode is

   pragma Preelaborate;

   type Pointer is private;
   --  A Pointer variable encapsulates a reference-counted accessor of
   --  type P (to a T).

   Null_Pointer : constant Pointer;
   --  Assign this to a Pointer when you've finished with its contents.

   function Create (Value : P) return Pointer;
   pragma Inline (Create);
   --  Returns a new encapsulation. You must NOT deallocate the Value
   --  passed; it will be deallocated when there are no more
   --  references to it.

   function Value (Ptr : Pointer) return P;
   pragma Inline (Value);
   --  returns the encapsulated pointer.

private
   pragma SPARK_Mode (Off);

   type Node is record
      Count : Natural := 0;
      Value : P;
   end record;
   type Ref is access Node;

   type Pointer is new Ada.Finalization.Controlled with record
      Rep : Ref;
   end record;

   procedure Adjust (Obj : in out Pointer);
   procedure Finalize (Obj : in out Pointer);

   Null_Pointer : constant Pointer
     := Pointer'(Ada.Finalization.Controlled with Rep => null);

end Aida.Generic_Shared_Ptr;
