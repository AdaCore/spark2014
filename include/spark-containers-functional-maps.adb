------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                    SPARK.CONTAINERS.FUNCTIONAL.MAPS                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2016-2022, Free Software Foundation, Inc.         --
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

pragma Ada_2012;

package body SPARK.Containers.Functional.Maps with SPARK_Mode => Off is
   use Key_Containers;
   use Element_Containers;

   package Conversions is new Signed_Conversions (Int => Count_Type);
   use Conversions;

   ---------
   -- "=" --
   ---------

   function "=" (Left : Map; Right : Map) return Boolean is
     (Length (Left.Keys) = Length (Right.Keys)
      and then Left <= Right);

   ----------
   -- "<=" --
   ----------

   function "<=" (Left : Map; Right : Map) return Boolean is
      I2 : Count_Type;

   begin
      if Length (Left.Keys) > Length (Right.Keys) then
         return False;
      elsif Ptr_Eq (Left.Keys, Right.Keys)
        and then Ptr_Eq (Left.Elements, Right.Elements)
      then
         return True;
      end if;

      for I1 in 1 .. Length (Left.Keys) loop
         I2 := Find (Right.Keys, Get (Left.Keys, I1));
         if I2 = 0
           or else Get (Right.Elements, I2) /= Get (Left.Elements, I1)
         then
            return False;
         end if;
      end loop;
      return True;
   end "<=";

   ---------
   -- Add --
   ---------

   function Add
     (Container : Map;
      New_Key   : Key_Type;
      New_Item  : Element_Type) return Map
   is
   begin
      return
        (Keys     =>
           Add (Container.Keys, Length (Container.Keys) + 1, New_Key),
         Elements =>
           Add
             (Container.Elements, Length (Container.Elements) + 1, New_Item));
   end Add;

   ------------
   -- Choose --
   ------------

   function Choose (Container : Map) return Key_Type is
     (Get (Container.Keys, Length (Container.Keys)));

   -------------------------
   -- Element_Logic_Equal --
   -------------------------

   function Element_Logic_Equal (Left, Right : Element_Type) return Boolean is
   begin
      Check_Or_Fail;
      return Left = Right;
   end Element_Logic_Equal;

   --------------------
   -- Elements_Equal --
   --------------------

   function Elements_Equal (Left, Right : Map) return Boolean is
   begin
      for J in 1 .. Length (Left.Keys) loop
         declare
            K : constant Key_Type := Get (Left.Keys, J);
         begin
            if Find (Right.Keys, K) = 0
              or else not Element_Logic_Equal
                (Get (Right.Elements, Find (Right.Keys, K)),
                 Get (Left.Elements, J))
            then
               return False;
            end if;
         end;
      end loop;
      return True;
   end Elements_Equal;

   ---------------------------
   -- Elements_Equal_Except --
   ---------------------------

   function Elements_Equal_Except
     (Left    : Map;
      Right   : Map;
      New_Key : Key_Type) return Boolean
   is
   begin
      for J in 1 .. Length (Left.Keys) loop
         declare
            K : constant Key_Type := Get (Left.Keys, J);
         begin
            if not Equivalent_Keys (K, New_Key)
              and then
                (Find (Right.Keys, K) = 0
                  or else not Element_Logic_Equal
                    (Get (Right.Elements, Find (Right.Keys, K)),
                     Get (Left.Elements, J)))
            then
               return False;
            end if;
         end;
      end loop;
      return True;
   end Elements_Equal_Except;

   function Elements_Equal_Except
     (Left  : Map;
      Right : Map;
      X     : Key_Type;
      Y     : Key_Type) return Boolean
   is
   begin
      for J in 1 .. Length (Left.Keys) loop
         declare
            K : constant Key_Type := Get (Left.Keys, J);
         begin
            if not Equivalent_Keys (K, X)
              and then not Equivalent_Keys (K, Y)
              and then
                (Find (Right.Keys, K) = 0
                  or else not Element_Logic_Equal
                    (Get (Right.Elements, Find (Right.Keys, K)),
                     Get (Left.Elements, J)))
            then
               return False;
            end if;
         end;
      end loop;
      return True;
   end Elements_Equal_Except;

   ---------------
   -- Empty_Map --
   ---------------

   function Empty_Map return Map is
      ((others =>  <>));

   ---------------------
   -- Equivalent_Maps --
   ---------------------

   function Equivalent_Maps (Left : Map; Right : Map) return Boolean is
      I2 : Count_Type;

   begin
      if Length (Left.Keys) /= Length (Right.Keys) then
         return False;
      elsif Ptr_Eq (Left.Keys, Right.Keys)
        and then Ptr_Eq (Left.Elements, Right.Elements)
      then
         return True;
      end if;

      for I1 in 1 .. Length (Left.Keys) loop
         I2 := Find (Right.Keys, Get (Left.Keys, I1));
         if I2 = 0
           or else not Equivalent_Elements
             (Get (Right.Elements, I2), Get (Left.Elements, I1))
         then
            return False;
         end if;
      end loop;
      return True;
   end Equivalent_Maps;

   ---------
   -- Get --
   ---------

   function Get (Container : Map; Key : Key_Type) return Element_Type is
   begin
      return Get (Container.Elements, Find_Rev (Container.Keys, Key));
   end Get;

   -------------
   -- Has_Key --
   -------------

   function Has_Key (Container : Map; Key : Key_Type) return Boolean is
   begin
      return Find_Rev (Container.Keys, Key) > 0;
   end Has_Key;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Map) return Boolean is
   begin
      return Length (Container.Keys) = 0;
   end Is_Empty;

   ------------------
   -- Iter_Element --
   ------------------

   function Iter_Element
     (Container : Map;
      Key       : Private_Key) return Key_Type
   is
   begin
      Check_Or_Fail;
      return Key_Containers.Get (Container.Keys, Count_Type (Key));
   end Iter_Element;

   ----------------
   -- Iter_First --
   ----------------

   function Iter_First (Container : Map) return Private_Key is
   begin
      Check_Or_Fail;
      return 1;
   end Iter_First;

   ----------------------
   -- Iter_Has_Element --
   ----------------------

   function Iter_Has_Element
     (Container : Map;
      Key       : Private_Key) return Boolean
   is
   begin
      Check_Or_Fail;
      return Count_Type (Key) in 1 .. Key_Containers.Length (Container.Keys);
   end Iter_Has_Element;

   ---------------
   -- Iter_Next --
   ---------------

   function Iter_Next
     (Container : Map;
      Key       : Private_Key) return Private_Key
   is
   begin
      Check_Or_Fail;
      return (if Key = Private_Key'Last then 0 else Key + 1);
   end Iter_Next;

   -------------------
   -- Keys_Included --
   -------------------

   function Keys_Included (Left : Map; Right : Map) return Boolean is
   begin
      for J in 1 .. Length (Left.Keys) loop
         declare
            K : constant Key_Type := Get (Left.Keys, J);
         begin
            if Find (Right.Keys, K) = 0 then
               return False;
            end if;
         end;
      end loop;

      return True;
   end Keys_Included;

   --------------------------
   -- Keys_Included_Except --
   --------------------------

   function Keys_Included_Except
     (Left    : Map;
      Right   : Map;
      New_Key : Key_Type) return Boolean
   is
   begin
      for J in 1 .. Length (Left.Keys) loop
         declare
            K : constant Key_Type := Get (Left.Keys, J);
         begin
            if not Equivalent_Keys (K, New_Key)
              and then Find (Right.Keys, K) = 0
            then
               return False;
            end if;
         end;
      end loop;

      return True;
   end Keys_Included_Except;

   function Keys_Included_Except
     (Left  : Map;
      Right : Map;
      X     : Key_Type;
      Y     : Key_Type) return Boolean
   is
   begin
      for J in 1 .. Length (Left.Keys) loop
         declare
            K : constant Key_Type := Get (Left.Keys, J);
         begin
            if not Equivalent_Keys (K, X)
              and then not Equivalent_Keys (K, Y)
              and then Find (Right.Keys, K) = 0
            then
               return False;
            end if;
         end;
      end loop;

      return True;
   end Keys_Included_Except;

   --------------------------
   -- Lemma_Get_Equivalent --
   --------------------------

   procedure Lemma_Get_Equivalent
     (Container    : Map;
      Key_1, Key_2 : Key_Type)
   is null;

   ------------------------------
   -- Lemma_Has_Key_Equivalent --
   ------------------------------

   procedure Lemma_Has_Key_Equivalent
     (Container : Map;
      Key       : Key_Type)
   is null;

   ------------
   -- Length --
   ------------

   function Length (Container : Map) return Big_Natural is
   begin
      return To_Big_Integer (Length (Container.Elements));
   end Length;

   ------------
   -- Remove --
   ------------

   function Remove (Container : Map; Key : Key_Type) return Map is
      J : constant Key_Containers.Extended_Index :=
        Find_Rev (Container.Keys, Key);
   begin
      return
        (Keys     => Remove (Container.Keys, J),
         Elements => Remove (Container.Elements, J));
   end Remove;

   ---------------
   -- Same_Keys --
   ---------------

   function Same_Keys (Left : Map; Right : Map) return Boolean is
     (Keys_Included (Left, Right)
       and Keys_Included (Left => Right, Right => Left));

   ---------
   -- Set --
   ---------

   function Set
     (Container : Map;
      Key       : Key_Type;
      New_Item  : Element_Type) return Map
   is
     (Keys     => Container.Keys,
      Elements =>
        Set (Container.Elements, Find (Container.Keys, Key), New_Item));

end SPARK.Containers.Functional.Maps;
