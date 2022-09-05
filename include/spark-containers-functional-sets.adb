------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                    SPARK.CONTAINERS.FUNCTIONAL.SETS                      --
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

package body SPARK.Containers.Functional.Sets with SPARK_Mode => Off is
   use Containers;

   package Conversions is new Signed_Conversions (Int => Count_Type);
   use Conversions;

   ---------
   -- "=" --
   ---------

   function "=" (Left : Set; Right : Set) return Boolean is
     (Length (Right) = Length (Left) and then Left.Content <= Right.Content);

   ----------
   -- "<=" --
   ----------

   function "<=" (Left : Set; Right : Set) return Boolean is
     (Left.Content <= Right.Content);

   ---------
   -- Add --
   ---------

   function Add (Container : Set; Item : Element_Type) return Set is
     (Content =>
       Add (Container.Content, Length (Container.Content) + 1, Item));

   --------------
   -- Contains --
   --------------

   function Contains (Container : Set; Item : Element_Type) return Boolean is
     (Find_Rev (Container.Content, Item) > 0);

   ------------
   -- Choose --
   ------------

   function Choose (Container : Set) return Element_Type is
     (Get (Container.Content, Length (Container.Content)));

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set return Set is
      ((others => <>));

   ---------------------
   -- Included_Except --
   ---------------------

   function Included_Except
     (Left  : Set;
      Right : Set;
      Item  : Element_Type) return Boolean
   is
     (for all E of Left =>
       Equivalent_Elements (E, Item) or Contains (Right, E));

   -----------------------
   -- Included_In_Union --
   -----------------------

   function Included_In_Union
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   is
     (for all Item of Container =>
       Contains (Left, Item) or Contains (Right, Item));

   ---------------------------
   -- Includes_Intersection --
   ---------------------------

   function Includes_Intersection
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   is
     (for all Item of Left =>
       (if Contains (Right, Item) then Contains (Container, Item)));

   ------------------
   -- Intersection --
   ------------------

   function Intersection (Left : Set; Right : Set) return Set is
     (Content => Intersection (Left.Content, Right.Content));

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Set) return Boolean is
     (Length (Container.Content) = 0);

   ------------------
   -- Is_Singleton --
   ------------------

   function Is_Singleton
     (Container : Set;
      New_Item  : Element_Type) return Boolean
   is
     (Length (Container.Content) = 1
        and New_Item = Get (Container.Content, 1));

   -------------------------------
   -- Lemma_Contains_Equivalent --
   -------------------------------

   procedure Lemma_Contains_Equivalent
     (Container : Set;
      Item      : Element_Type)
   is null;

   ------------
   -- Length --
   ------------

   function Length (Container : Set) return Big_Natural is
     (To_Big_Integer (Length (Container.Content)));

   -----------------
   -- Not_In_Both --
   -----------------

   function Not_In_Both
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   is
     (for all Item of Container =>
       not Contains (Right, Item) or not Contains (Left, Item));

   ----------------
   -- No_Overlap --
   ----------------

   function No_Overlap (Left : Set; Right : Set) return Boolean is
     (Num_Overlaps (Left.Content, Right.Content) = 0);

   ------------------
   -- Num_Overlaps --
   ------------------

   function Num_Overlaps (Left : Set; Right : Set) return Big_Natural is
     (To_Big_Integer (Num_Overlaps (Left.Content, Right.Content)));

   ------------
   -- Remove --
   ------------

   function Remove (Container : Set; Item : Element_Type) return Set is
     (Content =>
         Remove (Container.Content, Find_Rev (Container.Content, Item)));

   -----------
   -- Union --
   -----------

   function Union (Left : Set; Right : Set) return Set is
     (Content => Union (Left.Content, Right.Content));

end SPARK.Containers.Functional.Sets;
