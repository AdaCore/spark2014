pragma Ada_2022;

with Allocator;
with Allocator.Pools;
with Allocator.Pools.Sized_4;
with Allocator.Pools.Sized_8;
with Allocator.Pools.Sized_16;
with Allocator.Pools.Sized_32;
with Allocator.Pools.Sized_64;
with Interfaces; use Interfaces;

--  Prove instances of Allocator.Pools

package Test_Pools
  with SPARK_Mode
is
   Length_4  : constant Natural := 800;
   --  Maximal number of elements of size 4 that can be allocated in the buffer
   Length_8  : constant Natural := 400;
   --  Maximal number of elements of size 8 that can be allocated in the buffer
   Length_16 : constant Natural := 200;
   --  Maximal number of elements of size 16 that can be allocated in the buffer
   Length_32 : constant Natural := 100;
   --  Maximal number of elements of size 32 that can be allocated in the buffer
   Length_64 : constant Natural := 50;
   --  Maximal number of elements of size 64 that can be allocated in the buffer

   --  Create the pools

   package Pools is new
     Allocator.Pools
       (Length_4  => Length_4,
        Length_8  => Length_8,
        Length_16 => Length_16,
        Length_32 => Length_32,
        Length_64 => Length_64);

   type Object_Type_4 is record
      F1 : Unsigned_16;
      F2 : Boolean;
      F3 : Integer_8;
   end record
   with Object_Size => 32, Alignment => 4;

   package Object_Type_4_Allocator is new Pools.Sized_4 (Object_Type_4, 4);

   type Object_Type_8 is record
      F1 : Integer_32;
      F2 : Unsigned_16;
      F3 : Integer_8;
      F4 : Integer_8;
   end record
   with Object_Size => 64, Alignment => 4;

   package Object_Type_8_Allocator is new
     Pools.Sized_8 (Object_Type_8, 8, With_Promotion => False);

   type Object_Type_16 is record
      F1 : Integer_32;
      F2 : Unsigned_16;
      F3 : Boolean;
      F4 : Integer_8;
      F5 : Integer_64;
   end record
   with Object_Size => 128, Alignment => 4;

   package Object_Type_16_Allocator is new Pools.Sized_16 (Object_Type_16, 16);

   type Object_Type_32 is record
      F1 : Integer_32;
      F2 : Unsigned_16;
      F3 : Boolean;
      F4 : Integer_8;
      F5 : Integer_64;
      F6 : Unsigned_64;
   end record
   with Object_Size => 192, Alignment => 4;

   package Object_Type_32_Allocator is new Pools.Sized_32 (Object_Type_32, 24);

   type Unsigned_128_Arr is array (Positive range 1 .. 3) of Unsigned_128;

   type Object_Type_64 is record
      F1 : Integer_32;
      F2 : Unsigned_16;
      F3 : Boolean;
      F4 : Integer_8;
      F5 : Integer_64;
      F6 : Unsigned_128_Arr;
   end record
   with Object_Size => 512, Alignment => 4;

   package Object_Type_64_Allocator is new Pools.Sized_64 (Object_Type_64, 64);

end Test_Pools;
