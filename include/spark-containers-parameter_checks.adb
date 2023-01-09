------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                    SPARK.CONTAINERS.PARAMETER_CHECKS                     --
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

package body SPARK.Containers.Parameter_Checks with SPARK_Mode
is

   ------------------------
   -- Equivalence_Checks --
   ------------------------

   package body Equivalence_Checks is

      ------------------
      -- Eq_Reflexive --
      ------------------

      procedure Eq_Reflexive (X : T) is
      begin
         Param_Eq_Reflexive (X);
      end Eq_Reflexive;

      ------------------
      -- Eq_Symmetric --
      ------------------

      procedure Eq_Symmetric (X, Y : T) is
      begin
         Param_Eq_Symmetric (X, Y);
      end Eq_Symmetric;

      -------------------
      -- Eq_Transitive --
      -------------------

      procedure Eq_Transitive (X, Y, Z : T) is
      begin
         Param_Eq_Transitive (X, Y, Z);
      end Eq_Transitive;

   end Equivalence_Checks;

   ---------------------------
   -- Equivalence_Checks_Eq --
   ---------------------------

   package body Equivalence_Checks_Eq is

      ------------------
      -- Eq_Reflexive --
      ------------------

      procedure Eq_Reflexive (X : T) is
      begin
         Param_Equal_Reflexive (X);
         Eq_Reflexive (X, X);
      end Eq_Reflexive;

      procedure Eq_Reflexive (X, Y : T) is
      begin
         Param_Eq_Reflexive (X, Y);
      end Eq_Reflexive;

      ------------------
      -- Eq_Symmetric --
      ------------------

      procedure Eq_Symmetric (X, Y : T) is
      begin
         Param_Eq_Symmetric (X, Y);
      end Eq_Symmetric;

      -------------------
      -- Eq_Transitive --
      -------------------

      procedure Eq_Transitive (X, Y, Z : T) is
      begin
         Param_Eq_Transitive (X, Y, Z);
      end Eq_Transitive;

   end Equivalence_Checks_Eq;

   -------------------------------
   -- Hash_Compatibility_Checks --
   -------------------------------

   package body Hash_Compatibility_Checks is

      ---------------------
      -- Hash_Compatible --
      ---------------------

      procedure Hash_Compatible (X : T1) is
      begin
         Param_Hash_Compatible (X);
      end Hash_Compatible;

   end Hash_Compatibility_Checks;

   -----------------------------
   -- Hash_Equivalence_Checks --
   -----------------------------

   package body Hash_Equivalence_Checks is

      ---------------------
      -- Hash_Equivalent --
      ---------------------

      procedure Hash_Equivalent (X, Y : T) is
      begin
         Param_Hash_Equivalent (X, Y);
      end Hash_Equivalent;

   end Hash_Equivalence_Checks;

   -----------------------
   -- Lift_Eq_Reflexive --
   -----------------------

   package body Lift_Eq_Reflexive is

      ------------------
      -- Eq_Reflexive --
      ------------------

      procedure Eq_Reflexive (X, Y : T) is
      begin
         Param_Eq_Reflexive (X);
      end Eq_Reflexive;

   end Lift_Eq_Reflexive;

   -----------------------------
   -- Op_Compatibility_Checks --
   -----------------------------

   package body Op_Compatibility_Checks is

      -------------------
      -- Op_Compatible --
      -------------------

      procedure Op_Compatible (X, Y : T1) is
      begin
         Param_Op_Compatible (X, Y);
      end Op_Compatible;

   end Op_Compatibility_Checks;

   ------------------------------
   -- Strict_Weak_Order_Checks --
   ------------------------------

   package body Strict_Weak_Order_Checks is

      ------------------
      -- Eq_Reflexive --
      ------------------

      procedure Eq_Reflexive (X : T) is
      begin
         Lt_Irreflexive (X);
      end Eq_Reflexive;

      ------------------
      -- Eq_Symmetric --
      ------------------

      procedure Eq_Symmetric (X, Y : T) is null;

      -------------------
      -- Eq_Transitive --
      -------------------

      procedure Eq_Transitive (X, Y, Z : T) is
      begin
         if X < Z then
            Lt_Order (X, Z, Y);
            pragma Assert (False);
         elsif Z < X then
            Lt_Order (Z, X, Y);
            pragma Assert (False);
         end if;
      end Eq_Transitive;

      -------------------
      -- Lt_Asymmetric --
      -------------------

      procedure Lt_Asymmetric (X, Y : T) is
      begin
         Param_Lt_Asymmetric (X, Y);
      end Lt_Asymmetric;

      --------------------
      -- Lt_Irreflexive --
      --------------------

      procedure Lt_Irreflexive (X : T) is
      begin
         Param_Lt_Irreflexive (X);
      end Lt_Irreflexive;

      --------------
      -- Lt_Order --
      --------------

      procedure Lt_Order (X, Y, Z : T) is
      begin
         Param_Lt_Order (X, Y, Z);
      end Lt_Order;

      -------------------
      -- Lt_Transitive --
      -------------------

      procedure Lt_Transitive (X, Y, Z : T) is
      begin
         Param_Lt_Transitive (X, Y, Z);
      end Lt_Transitive;

   end Strict_Weak_Order_Checks;

   ---------------------------------
   -- Strict_Weak_Order_Checks_Eq --
   ---------------------------------

   package body Strict_Weak_Order_Checks_Eq is

      ------------------
      -- Eq_Reflexive --
      ------------------

      procedure Eq_Reflexive (X : T) is
      begin
         Param_Eq_Reflexive (X);
         Lt_Irreflexive (X, X);
      end Eq_Reflexive;

      procedure Eq_Reflexive (X, Y : T) is
      begin
         Lt_Irreflexive (X, Y);
         Param_Eq_Symmetric (X, Y);
         Lt_Irreflexive (Y, X);
      end Eq_Reflexive;

      ------------------
      -- Eq_Symmetric --
      ------------------

      procedure Eq_Symmetric (X, Y : T) is null;

      -------------------
      -- Eq_Transitive --
      -------------------

      procedure Eq_Transitive (X, Y, Z : T) is
      begin
         if X < Z then
            Lt_Order (X, Z, Y);
            pragma Assert (False);
         elsif Z < X then
            Lt_Order (Z, X, Y);
            pragma Assert (False);
         end if;
      end Eq_Transitive;

      -------------------
      -- Lt_Asymmetric --
      -------------------

      procedure Lt_Asymmetric (X, Y : T) is
      begin
         Param_Lt_Asymmetric (X, Y);
      end Lt_Asymmetric;

      --------------------
      -- Lt_Irreflexive --
      --------------------

      procedure Lt_Irreflexive (X, Y : T) is
      begin
         Param_Lt_Irreflexive (X, Y);
      end Lt_Irreflexive;

      --------------
      -- Lt_Order --
      --------------

      procedure Lt_Order (X, Y, Z : T) is
      begin
         Param_Lt_Order (X, Y, Z);
      end Lt_Order;

      -------------------
      -- Lt_Transitive --
      -------------------

      procedure Lt_Transitive (X, Y, Z : T) is
      begin
         Param_Lt_Transitive (X, Y, Z);
      end Lt_Transitive;

   end Strict_Weak_Order_Checks_Eq;

end SPARK.Containers.Parameter_Checks;
