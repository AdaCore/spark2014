with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers.Formal_Vectors;
with Ada.Containers.Formal_Indefinite_Vectors;
with Ada.Containers.Formal_Hashed_Sets;
with Ada.Containers.Formal_Ordered_Sets;
with Ada.Containers.Formal_Hashed_Maps;
with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers.Functional_Vectors;
with Ada.Containers.Functional_Sets;
with Ada.Containers.Functional_Maps;

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

   package Lists is new Ada.Containers.Formal_Doubly_Linked_Lists (Holder);
   package Sequences is new Ada.Containers.Functional_Vectors (Positive, Holder);
   package Vectors is new Ada.Containers.Formal_Vectors (Positive, Holder);
   package Indef_Vectors is new Ada.Containers.Formal_Indefinite_Vectors (Positive, Holder, Max_Size_In_Storage_Elements => Holder'Size);
   package H_Sets is new Ada.Containers.Formal_Hashed_Sets (Holder, Hash);
   package O_Sets is new Ada.Containers.Formal_Ordered_Sets (Holder);
   package F_Sets is new Ada.Containers.Functional_Sets (Holder);
   package H_Maps_1 is new Ada.Containers.Formal_Hashed_Maps (Positive, Holder, Hash);
   package O_Maps_1 is new Ada.Containers.Formal_Ordered_Maps (Positive, Holder);
   package F_Maps_1 is new Ada.Containers.Functional_Maps (Positive, Holder);
   package H_Maps_2 is new Ada.Containers.Formal_Hashed_Maps (Holder, Positive, Hash);
   package O_Maps_2 is new Ada.Containers.Formal_Ordered_Maps (Holder, Positive);
   package F_Maps_2 is new Ada.Containers.Functional_Maps (Holder, Positive);
begin
   null;
end Test_Deep_Element_Type;
