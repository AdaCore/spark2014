with Ada.Containers.Formal_Hashed_Maps;
with Ada.Containers; use Ada.Containers;

package My_Maps with SPARK_Mode is

   function Hash (Id : Natural) return Hash_Type is (Hash_Type (Id));

   package M is new Ada.Containers.Formal_Hashed_Maps
     (Element_Type    => Integer,
      Key_Type        => Positive,
      Hash            => Hash,
      Equivalent_Keys => "=");

   type My_Rec is record
      F : Positive;
      G : Integer;
   end record;

   function My_Eq (X, Y : My_Rec) return Boolean is (X.F = Y.F)
   with Post => My_Eq'Result = (X.F = Y.F);
   pragma Annotate (GNATprove, Inline_For_Proof, My_Eq);

   function Hash (Id : My_Rec) return Hash_Type is (Hash_Type (Id.F));

   package N is new Ada.Containers.Formal_Hashed_Maps
     (Element_Type    => Integer,
      Key_Type        => My_Rec,
      Hash            => Hash,
      Equivalent_Keys => My_Eq);

   procedure Test_Map;
end My_Maps;
