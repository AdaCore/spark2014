------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                    SPARK.CONTAINERS.PARAMETER_CHECKS                     --
--                                                                          --
--                                 S p e c                                  --
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

--  This package contains generic ghost packages used to check that the
--  parameters of the container library respect their assumptions.

with SPARK.Containers.Types; use SPARK.Containers.Types;

package SPARK.Containers.Parameter_Checks with
  SPARK_Mode,
  Ghost
is

   --  Check that Eq is an equivalence relation. It shall be reflexive,
   --  symmetric, and transitive.

   generic
      type T (<>) is private;
      with function Eq (Left, Right : T) return Boolean;

      with procedure Param_Eq_Reflexive (X : T);
      with procedure Param_Eq_Symmetric (X, Y : T);
      with procedure Param_Eq_Transitive (X, Y, Z : T);

   package Equivalence_Checks is

      procedure Eq_Reflexive (X : T) with
        Global => null,
        Post   => Eq (X, X);

      procedure Eq_Symmetric (X, Y : T) with
        Global => null,
        Pre    => Eq (X, Y),
        Post   => Eq (Y, X);

      procedure Eq_Transitive (X, Y, Z : T) with
        Global => null,
        Pre    => Eq (X, Y) and Eq (Y, Z),
        Post   => Eq (X, Z);

   end Equivalence_Checks;

   --  Check that Eq is an equivalence relation with respect to an equality
   --  function "=". The "=" parameter is used to express the reflexivity
   --  property.

   generic
      type T (<>) is private;
      with function Eq (Left, Right : T) return Boolean;
      with function "=" (Left, Right : T) return Boolean;

      with procedure Param_Equal_Reflexive (X : T);
      with procedure Param_Eq_Reflexive (X, Y : T);
      with procedure Param_Eq_Symmetric (X, Y : T);
      with procedure Param_Eq_Transitive (X, Y, Z : T);

   package Equivalence_Checks_Eq is

      procedure Eq_Reflexive (X, Y : T) with
        Global => null,
        Pre    => X = Y,
        Post   => Eq (X, Y);

      --  The binary version of Eq_Reflexive is always enough to prove its
      --  unary version.

      procedure Eq_Reflexive (X : T) with
        Global => null,
        Post   => Eq (X, X);

      procedure Eq_Symmetric (X, Y : T) with
        Global => null,
        Pre    => Eq (X, Y),
        Post   => Eq (Y, X);

      procedure Eq_Transitive (X, Y, Z : T) with
        Global => null,
        Pre    => Eq (X, Y) and Eq (Y, Z),
        Post   => Eq (X, Z);

   end Equivalence_Checks_Eq;

   --  Check that the unary version of Eq_Reflexive is enough to prove its
   --  binary version. This is typically the case if "=" is the logical
   --  equality on T.

   generic
      type T (<>) is private;
      with function "=" (Left, Right : T) return Boolean;
      with function Eq (Left, Right : T) return Boolean;

      with procedure Param_Eq_Reflexive (X : T);

   package Lift_Eq_Reflexive is

      procedure Eq_Reflexive (X, Y : T) with
        Global => null,
        Pre    => X = Y,
        Post   => Eq (X, Y);

   end Lift_Eq_Reflexive;

   --  Check that "<" is a strict weak ordering relationship. It shall be
   --  irreflexive, asymmetric, transitive, and in addition, if x < y for any
   --  values x and y, then for all other values z, either (x < z) or (z < y)
   --  or both.

   generic
      type T (<>) is private;
      with function "<" (Left, Right : T) return Boolean;

      with procedure Param_Lt_Irreflexive (X : T);
      with procedure Param_Lt_Asymmetric (X, Y : T);
      with procedure Param_Lt_Transitive (X, Y, Z : T);
      with procedure Param_Lt_Order (X, Y, Z : T);

   package Strict_Weak_Order_Checks is

      procedure Lt_Irreflexive (X : T) with
        Global => null,
        Post   => not (X < X);

      procedure Lt_Asymmetric (X, Y : T) with
        Global => null,
        Pre    => X < Y,
        Post   => not (Y < X);

      procedure Lt_Transitive (X, Y, Z : T) with
        Global => null,
        Pre    => X < Y and Y < Z,
        Post   => X < Z;

      procedure Lt_Order (X, Y, Z : T) with
        Global => null,
        Pre    => X < Y,
        Post   => X < Z or Z < Y;

      --  Prove that the equivalence relation induced by "<" is an equivalence
      --  relation. This is necessarily True if "<" is a weak order and "=" is
      --  an equivalence relation.

      function Eq (X, Y : T) return Boolean is (not (X < Y) and not (Y < X));

      procedure Eq_Reflexive (X : T) with
        Global => null,
        Post   => Eq (X, X);

      procedure Eq_Symmetric (X, Y : T) with
        Global => null,
        Pre    => Eq (X, Y),
        Post   => Eq (Y, X);

      procedure Eq_Transitive (X, Y, Z : T) with
        Global => null,
        Pre    => Eq (X, Y) and Eq (Y, Z),
        Post   => Eq (X, Z);

   end Strict_Weak_Order_Checks;

   --  Check that "<" is a strict weak ordering relationship with respect to an
   --  equality function "=". The "=" parameter is used to express the
   --  irreflexivity property.

   generic
      type T (<>) is private;
      with function "=" (Left, Right : T) return Boolean;
      with function "<" (Left, Right : T) return Boolean;

      with procedure Param_Eq_Reflexive (X : T) is null;
      with procedure Param_Eq_Symmetric (X, Y : T) is null;
      with procedure Param_Lt_Irreflexive (X, Y : T);
      with procedure Param_Lt_Asymmetric (X, Y : T);
      with procedure Param_Lt_Transitive (X, Y, Z : T);
      with procedure Param_Lt_Order (X, Y, Z : T);

   package Strict_Weak_Order_Checks_Eq is

      procedure Lt_Irreflexive (X, Y : T) with
        Global => null,
        Pre    => X = Y,
        Post   => not (X < Y);

      procedure Lt_Asymmetric (X, Y : T) with
        Global => null,
        Pre    => X < Y,
        Post   => not (Y < X);

      procedure Lt_Transitive (X, Y, Z : T) with
        Global => null,
        Pre    => X < Y and Y < Z,
        Post   => X < Z;

      procedure Lt_Order (X, Y, Z : T) with
        Global => null,
        Pre    => X < Y,
        Post   => X < Z or Z < Y;

      --  Prove that the equivalence relation induced by "<" is an equivalence
      --  relation. This is necessarily True if "<" is a weak order and "=" is
      --  an equivalence relation.

      function Eq (X, Y : T) return Boolean is (not (X < Y) and not (Y < X));

      procedure Eq_Reflexive (X : T) with
        Global => null,
        Post   => Eq (X, X);

      procedure Eq_Reflexive (X, Y : T) with
        Global => null,
        Pre    => X = Y,
        Post   => Eq (X, Y);

      procedure Eq_Symmetric (X, Y : T) with
        Global => null,
        Pre    => Eq (X, Y),
        Post   => Eq (Y, X);

      procedure Eq_Transitive (X, Y, Z : T) with
        Global => null,
        Pre    => Eq (X, Y) and Eq (Y, Z),
        Post   => Eq (X, Z);

   end Strict_Weak_Order_Checks_Eq;

   --  Check that Hash returns the same value for all equivalent elements

   generic
      type T (<>) is private;
      with function "=" (Left, Right : T) return Boolean;
      with function Hash (X : T) return Hash_Type;

      with procedure Param_Hash_Equivalent (X, Y : T);

   package Hash_Equivalence_Checks is

      procedure Hash_Equivalent (X, Y : T) with
        Global => null,
        Pre    => X = Y,
        Post   => Hash (X) = Hash (Y);

   end Hash_Equivalence_Checks;

   --  Check that two binary operators Op1 and Op2 on two types T1 and T2 are
   --  compatible with respect to a conversion function F.

   generic
      type T1 (<>) is private;
      type T2 (<>) is private;
      with function Op1 (Left, Right : T1) return Boolean;
      with function Op2 (Left, Right : T2) return Boolean;
      with function F (X : T1) return T2;

      with procedure Param_Op_Compatible (X, Y : T1);

   package Op_Compatibility_Checks is

      procedure Op_Compatible (X, Y : T1) with
        Global => null,
        Post   => Op1 (X, Y) = Op2 (F (X), F (Y));

   end Op_Compatibility_Checks;

   --  Check that two hash functions Hash1 and Hash2 on two types T1 and T2 are
   --  compatible with respect to a conversion function F.

   generic
      type T1 (<>) is private;
      type T2 (<>) is private;
      with function Hash1 (X : T1) return Hash_Type;
      with function Hash2 (X : T2) return Hash_Type;
      with function F (X : T1) return T2;

      with procedure Param_Hash_Compatible (X : T1);

   package Hash_Compatibility_Checks is

      procedure Hash_Compatible (X : T1) with
        Global => null,
        Post   => Hash1 (X) = Hash2 (F (X));

   end Hash_Compatibility_Checks;

end SPARK.Containers.Parameter_Checks;
