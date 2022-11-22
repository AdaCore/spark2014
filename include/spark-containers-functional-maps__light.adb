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

--  This body is provided as a work-around for a GNAT compiler bug, as GNAT
--  currently does not compile instantiations of the spec with imported ghost
--  generics.

pragma Ada_2012;
package body SPARK.Containers.Functional.Maps with SPARK_Mode => Off is

   ---------
   -- "=" --
   ---------

   function "=" (Left : Map; Right : Map) return Boolean is
     (raise Program_Error);

   ----------
   -- "<=" --
   ----------

   function "<=" (Left : Map; Right : Map) return Boolean is
     (raise Program_Error);

   ---------
   -- Add --
   ---------

   function Add
     (Container : Map;
      New_Key   : Key_Type;
      New_Item  : Element_Type) return Map
   is
     (raise Program_Error);

   ------------
   -- Choose --
   ------------

   function Choose (Container : Map) return Key_Type is
     (raise Program_Error);

   ---------------------------
   -- Elements_Equal_Except --
   ---------------------------

   function Elements_Equal_Except
     (Left    : Map;
      Right   : Map;
      New_Key : Key_Type) return Boolean
   is
     (raise Program_Error);

   function Elements_Equal_Except
     (Left  : Map;
      Right : Map;
      X     : Key_Type;
      Y     : Key_Type) return Boolean
   is
     (raise Program_Error);

   ---------------
   -- Empty_Map --
   ---------------

   function Empty_Map return Map is
     (raise Program_Error);

   ---------
   -- Get --
   ---------

   function Get (Container : Map; Key : Key_Type) return Element_Type is
     (raise Program_Error);

   -------------
   -- Has_Key --
   -------------

   function Has_Key (Container : Map; Key : Key_Type) return Boolean is
     (raise Program_Error);

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Map) return Boolean is
     (raise Program_Error);

   -------------------
   -- Keys_Included --
   -------------------

   function Keys_Included (Left : Map; Right : Map) return Boolean is
     (raise Program_Error);

   --------------------------
   -- Keys_Included_Except --
   --------------------------

   function Keys_Included_Except
     (Left    : Map;
      Right   : Map;
      New_Key : Key_Type) return Boolean
   is
     (raise Program_Error);

   function Keys_Included_Except
     (Left  : Map;
      Right : Map;
      X     : Key_Type;
      Y     : Key_Type) return Boolean
   is
     (raise Program_Error);

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
     (raise Program_Error);

   ------------
   -- Remove --
   ------------

   function Remove (Container : Map; Key : Key_Type) return Map is
     (raise Program_Error);

   ---------------
   -- Same_Keys --
   ---------------

   function Same_Keys (Left : Map; Right : Map) return Boolean is
     (raise Program_Error);

   ---------
   -- Set --
   ---------

   function Set
     (Container : Map;
      Key       : Key_Type;
      New_Item  : Element_Type) return Map
   is
     (raise Program_Error);

end SPARK.Containers.Functional.Maps;
