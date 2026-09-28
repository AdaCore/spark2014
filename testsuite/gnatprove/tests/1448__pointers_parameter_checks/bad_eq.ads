pragma Ada_2022;

with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Sets;
with SPARK.Pointers.Abstract_Maps;
with SPARK.Pointers.Abstract_Reachability;

--  The "=" supplied to Abstract_Reachability shall be the logical equality on
--  keys. The one below is an equivalence relation but not the logical equality.
--  The formal package of Abstract_Reachability is an instance of
--  Infinite_Sequences with Use_Logical_Equality => True, so it will necessarily
--  produce a failed check.

package Bad_Eq with SPARK_Mode is

   type Key_Type is record
      V : Integer;
   end record;

   --  Keys with the same parity are identified. Declared before Key_Type is
   --  frozen, as RM 4.5.2(9.8) requires.

   function "=" (Left, Right : Key_Type) return Boolean
   is (Left.V mod 2 = Right.V mod 2)
   with Global => null;

   No_Key : constant Key_Type := (V => 0);

   type Object_Type is record
      N : Key_Type;
   end record;

   function Next (O : Object_Type) return Key_Type
   is (O.N)
   with Global => null, Ghost => Static;

   package Memory_Maps is new
     SPARK.Pointers.Abstract_Maps (Key_Type, No_Key, Object_Type);

   package Ghost_Containers with Ghost => Static is
      package Key_Sets is new SPARK.Containers.Functional.Sets (Key_Type, "=");
      package Key_Sequences is new
        SPARK.Containers.Functional.Infinite_Sequences
          (Key_Type, "=", Use_Logical_Equality => True);
   end Ghost_Containers;
   use Ghost_Containers;

   package Reach is new
     SPARK.Pointers.Abstract_Reachability
       (Memory_Maps   => Memory_Maps,
        "="           => "=",
        Next          => Next,
        Key_Sets      => Key_Sets,
        Key_Sequences => Key_Sequences);

end Bad_Eq;
