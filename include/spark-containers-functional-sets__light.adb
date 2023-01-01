------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                    SPARK.CONTAINERS.FUNCTIONAL.SETS                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2016-2023, Free Software Foundation, Inc.         --
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

--  This body is provided as a work-around for a GNAT compiler bug, as GNAT
--  currently does not compile instantiations of the spec with imported ghost
--  generics.

pragma Ada_2012;

package body SPARK.Containers.Functional.Sets with SPARK_Mode => Off is

   ---------
   -- "=" --
   ---------

   function "=" (Left : Set; Right : Set) return Boolean is
     (raise Program_Error);

   ----------
   -- "<=" --
   ----------

   function "<=" (Left : Set; Right : Set) return Boolean is
     (raise Program_Error);

   ---------
   -- Add --
   ---------

   function Add (Container : Set; Item : Element_Type) return Set is
     (raise Program_Error);

   --------------
   -- Contains --
   --------------

   function Contains (Container : Set; Item : Element_Type) return Boolean is
     (raise Program_Error);

   ------------
   -- Choose --
   ------------

   function Choose (Container : Set) return Element_Type is
     (raise Program_Error);

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set return Set is
     (raise Program_Error);

   ---------------------
   -- Included_Except --
   ---------------------

   function Included_Except
     (Left  : Set;
      Right : Set;
      Item  : Element_Type) return Boolean
   is
     (raise Program_Error);

   -----------------------
   -- Included_In_Union --
   -----------------------

   function Included_In_Union
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   is
     (raise Program_Error);

   ---------------------------
   -- Includes_Intersection --
   ---------------------------

   function Includes_Intersection
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   is
     (raise Program_Error);

   ------------------
   -- Intersection --
   ------------------

   function Intersection (Left : Set; Right : Set) return Set is
     (raise Program_Error);

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Set) return Boolean is
     (raise Program_Error);

   ------------------
   -- Is_Singleton --
   ------------------

   function Is_Singleton
     (Container : Set;
      New_Item  : Element_Type) return Boolean
   is
     (raise Program_Error);

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
     (raise Program_Error);

   -----------------
   -- Not_In_Both --
   -----------------

   function Not_In_Both
     (Container : Set;
      Left      : Set;
      Right     : Set) return Boolean
   is
     (raise Program_Error);

   ----------------
   -- No_Overlap --
   ----------------

   function No_Overlap (Left : Set; Right : Set) return Boolean is
     (raise Program_Error);

   ------------------
   -- Num_Overlaps --
   ------------------

   function Num_Overlaps (Left : Set; Right : Set) return Big_Natural is
     (raise Program_Error);

   ------------
   -- Remove --
   ------------

   function Remove (Container : Set; Item : Element_Type) return Set is
     (raise Program_Error);

   -----------
   -- Union --
   -----------

   function Union (Left : Set; Right : Set) return Set is
     (raise Program_Error);

end SPARK.Containers.Functional.Sets;
