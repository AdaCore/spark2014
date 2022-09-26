with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Formal.Doubly_Linked_Lists;
with SPARK.Containers.Formal.Vectors;
with SPARK.Containers.Formal.Unbounded_Vectors;
with SPARK.Containers.Formal.Hashed_Sets;
with SPARK.Containers.Formal.Ordered_Sets;
with SPARK.Containers.Formal.Hashed_Maps;
with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Maps;

procedure Test_Deep_Element_Type with SPARK_Mode is
   type Pos_Acc is access Positive;
   type Wrapper is record
      C : Pos_Acc;
   end record;
   function "=" (X, Y : Wrapper) return Boolean is
     ((X.C = null) = (Y.C = null)
      and then (if X.C /= null then X.C.all = Y.C.all));

   type Holder is record
      Content : Wrapper;
   end record;

   function "<" (X, Y : Holder) return Boolean is
     (Y.Content.C /= null
      and then (if X.Content.C /= null then X.Content.C.all < Y.Content.C.all));

   function Hash (X : Holder) return Hash_Type is
      (if X.Content.C = null then 0 else Hash_Type (X.Content.C.all));
   function Hash (X : Positive) return Hash_Type is
      (Hash_Type (X));

   package Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Holder);
   package Sequences is new SPARK.Containers.Functional.Vectors (Positive, Holder);
   package Vectors is new SPARK.Containers.Formal.Vectors (Positive, Holder);
   package Indef_Vectors is new SPARK.Containers.Formal.Unbounded_Vectors (Positive, Holder);
   package H_Sets is new SPARK.Containers.Formal.Hashed_Sets (Holder, Hash);
   package O_Sets is new SPARK.Containers.Formal.Ordered_Sets (Holder);
   package F_Sets is new SPARK.Containers.Functional.Sets (Holder);
   package H_Maps_1 is new SPARK.Containers.Formal.Hashed_Maps (Positive, Holder, Hash);
   package O_Maps_1 is new SPARK.Containers.Formal.Ordered_Maps (Positive, Holder);
   package F_Maps_1 is new SPARK.Containers.Functional.Maps (Positive, Holder);
   package H_Maps_2 is new SPARK.Containers.Formal.Hashed_Maps (Holder, Positive, Hash);
   package O_Maps_2 is new SPARK.Containers.Formal.Ordered_Maps (Holder, Positive);
   package F_Maps_2 is new SPARK.Containers.Functional.Maps (Holder, Positive);
begin
   null;
end Test_Deep_Element_Type;
