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

pragma Ada_2012;
with Ada.Containers;
with Ada.Numerics.Discrete_Random;
with System.Storage_Pools;  use System.Storage_Pools;
with System.Pool_Global;

package Conts with SPARK_Mode is

   type Count_Type is range 0 .. 2 ** 31 - 1;
   subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
   subtype Hash_Type is Ada.Containers.Hash_Type;    --  0 .. 2**32 - 1
   --  Base types for the size of containers, and the hash values used
   --  for some containers. We reuse the same values as for Ada.Containers,
   --  but redefine the type here so that it is possible to change to
   --  other values on specific architectures, for instance, without
   --  breaking code that would assume this Count_Type to always be the
   --  same as Ada.Containers.Count_Type.
   --  For now, various places in the code assume that
   --     Count_Type'Last * 2 <= Hash_Type'Last
   --  since we often cast from the latter to the former to get a greater
   --  range.

   type Limited_Base is abstract tagged limited null record;
   --  A type that can be used as the root of a container hierarchy when a
   --  container should be limited (and thus prevent its copying).
   --  Other containers will in general derive from
   --  Ada.Finalization.Controlled.

   -------------------
   -- Storage pools --
   -------------------

   generic
      type Storage_Pool is new Root_Storage_Pool with private;
      Pool : in out Storage_Pool;
   package Pools with SPARK_Mode => Off is
   end Pools;
   --  This package provides a way to pass storage pools as a generic parameter
   --  to other packages.
   --  Such storage pools are limited types, and thus need to be passed as
   --  access types. Furthermore, to avoid the need for dynamic dispatching, we
   --  also pass the type of the storage pool itself, rather than use a class
   --  wide type.

   package Global_Pool is new Pools
      (Storage_Pool  => System.Pool_Global.Unbounded_No_Reclaim_Pool,
       Pool => System.Pool_Global.Global_Pool_Object);
   --  The default storage pool used by the GNAT runtime (a direct use of
   --  malloc and free).

   --------------------
   -- Random numbers --
   --------------------

   generic
      type Discrete_Type is (<>);
      type Generator_Type is limited private;
      with procedure Random
         (Self : in out Generator_Type; Result : out Discrete_Type);
   package Uniform_Random_Traits is
      subtype Discrete is Discrete_Type;
      subtype Generator is Generator_Type;
      procedure Rand
         (Self : in out Generator; Result : out Discrete) renames Random;
   end Uniform_Random_Traits;
   --  Generates a uniformly distributed random number on the whole range of
   --  Discrete. This could a simple wrapper around Ada's standard facilities
   --  (see below for such a pre-made wrapper), or a custom implementation (for
   --  instance a reproducible sequence for use in some testsuites).
   --
   --  Random is implemented as a procedure, not a function, so that it is
   --  easier to use for proofs in the SPARK context.

   generic
      with package Random is new Uniform_Random_Traits (<>);
      Min, Max : Random.Discrete;
   procedure Ranged_Random
      (Self : in out Random.Generator; Result : out Random.Discrete)
      with Inline;
   --  Returns a random number in the range Min..Max
   --  This is optimized so that if this range is the full range for the
   --  discrete type, no additional test or operation is needed. Thus
   --  algorithms should take a Uniform_Random_Traits, and instantiate this
   --  function as needed.
   --  This is similar to the GNAT.Random package, but since the range is
   --  given by formal parameters, the compiler can optimize the code
   --  significantly more.

   generic
      type Discrete_Type is (<>);
   package Default_Random is
      package Ada_Random is new Ada.Numerics.Discrete_Random (Discrete_Type);

      subtype Generator is Ada_Random.Generator;
      procedure Reset (Gen : Generator) renames Ada_Random.Reset;
      procedure Reset (Gen : Generator; Initiator : Integer)
         renames Ada_Random.Reset;
      --  Used by applications, but not directly by this library, since
      --  algorithms always take an already initialized generator as parameter

      procedure Random (Gen : in out Generator; Result : out Discrete_Type)
         with Inline;
      --  Wrapper around Ada_Random.Random

      package Traits is new Uniform_Random_Traits
        (Discrete_Type  => Discrete_Type,
         Generator_Type => Generator,
         Random         => Random);
   end Default_Random;
   --  A default implementation of random numbers based on the standard Ada
   --  random number generator.

end Conts;
