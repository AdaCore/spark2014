with Ada.Containers;
with Ada.Containers.Formal_Vectors;
with Ada.Containers.Formal_Hashed_Maps;

procedure Prim_Eq_Vect with SPARK_Mode is
   package Int_Vect is new Ada.Containers.Formal_Vectors
     (Index_Type => Positive, Element_Type => Integer);
   use all type Int_Vect.Vector;
   subtype My_Vect is Int_Vect.Vector (Capacity => 200);

   type Two_Vects is record
      F, G : My_Vect;
   end record;

   function My_Hash (X : Integer) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type'Mod (X));

   package Int_Vect_Map is new Ada.Containers.Formal_Hashed_Maps
     (Key_Type        => Integer,
      Element_Type    => Two_Vects,
      Hash            => My_Hash,
      Equivalent_Keys => "=");
   use all type Int_Vect_Map.Map;

   procedure P (X, Y : Int_Vect_Map.Map; Id : Integer) with
     Ghost,
     Pre => X = Y and Int_Vect_Map.Contains (X, Id),
     Post => Int_Vect_Map.Element (X, Id).F = Int_Vect_Map.Element (Y, Id).F;

   procedure P (X, Y : Int_Vect_Map.Map; Id : Integer) is null;
begin
   null;
end Prim_Eq_Vect;
