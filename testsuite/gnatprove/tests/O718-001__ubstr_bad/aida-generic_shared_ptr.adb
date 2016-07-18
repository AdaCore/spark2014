-- This smart pointers implementation originates from Booch Components
-- and it has the following copyright notice:
--
--  Copyright 1998-2011 Simon Wright <simon@pushface.org>
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
--  $Revision: 1450 $
--  $Date: 2011-02-13 21:29:13 +0000 (Sun, 13 Feb 2011) $
--  $Author: simonjwright $

with Ada.Unchecked_Deallocation;

package body Aida.Generic_Shared_Ptr is

   function Create (Value : P) return Pointer is
   begin
      return Pointer'(Ada.Finalization.Controlled
                      with Rep => new Node'(Count => 1,
                                            Value => Value));
   end Create;

   function Value (Ptr : Pointer) return P is
   begin
      if Ptr.Rep = null then
         return null;
      else
         return Ptr.Rep.Value;
      end if;
   end Value;

   procedure Adjust (Obj : in out Pointer) is
   begin
      if Obj.Rep /= null then
         Obj.Rep.Count := Obj.Rep.Count + 1;
      end if;
   end Adjust;

   procedure Delete is new Ada.Unchecked_Deallocation (T, P);
   procedure Delete is new Ada.Unchecked_Deallocation (Node, Ref);

   --  Finalize may be called more than once on the same object.
   --
   --  The first time it's called, we may set Tmp to a non-null value
   --  which designates the actual shared object and then proceed to
   --  decrement the count and, if no references remain, delete the
   --  used memory. But, in any case, *this* smart pointer no longer
   --  references the actual object, so another call to Finalize will
   --  have no effect.
   procedure Finalize (Obj : in out Pointer) is
      Tmp : Ref := Obj.Rep;
   begin
      Obj.Rep := null;
      if Tmp /= null then
         Tmp.Count := Tmp.Count - 1;
         if Tmp.Count = 0 then
            Delete (Tmp.Value);
            Delete (Tmp);
         end if;
      end if;
   end Finalize;

end Aida.Generic_Shared_Ptr;
