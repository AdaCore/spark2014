with Ada.Containers.Formal_Hashed_Sets;
with Ada.Containers; use Ada.Containers;

package My_Sets with SPARK_Mode is

   function Hash (Id : Natural) return Hash_Type is (Hash_Type (Id));

   package M is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type        => Positive,
      Hash                => Hash,
      Equivalent_Elements => "=");

   type My_Rec is record
      F : Positive;
      G : Integer;
   end record;

   function My_Eq (X, Y : My_Rec) return Boolean is (X.F = Y.F)
   with Post => My_Eq'Result = (X.F = Y.F);
   pragma Annotate (GNATprove, Inline_For_Proof, My_Eq);

   function Hash (Id : My_Rec) return Hash_Type is (Hash_Type (Id.F));

   package N is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type        => My_Rec,
      Hash                => Hash,
      Equivalent_Elements => My_Eq);

   function Get_F (X : My_Rec) return Positive is (X.F)
   with Post => Get_F'Result = X.F;
   pragma Annotate (GNATprove, Inline_For_Proof, Get_F);

   package G is new N.Generic_Keys
     (Key_Type        => Positive,
      Key             => Get_F,
      Hash            => Hash,
      Equivalent_Keys => "=");

   procedure Test_Set;
end My_Sets;
