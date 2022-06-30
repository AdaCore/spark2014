with SPARK.Containers.Formal.Hashed_Maps;
with Ada.Containers;
with Ada.Strings.Hash;

package P
is
   subtype My_String is String (1 .. 5);

   type My_Id is range 1 .. 1000;

   type My_Mapping is private;

   procedure Clear (Map : out My_Mapping);

   function Contains (Map : My_Mapping;
                      Key : My_String) return Boolean;

private

   package My_Hash is new SPARK.Containers.Formal.Hashed_Maps
     (Key_Type        => My_String,
      Element_Type    => My_Id,
      Hash            => Ada.Strings.Hash,
      Equivalent_Keys => "=");

   Capacity : constant Ada.Containers.Count_Type :=
     Ada.Containers.Count_Type (My_Id'Last);
   Modulus  : constant Ada.Containers.Hash_Type :=
     My_Hash.Default_Modulus (Ada.Containers.Count_Type (My_Id'Last));

   subtype My_Hash_Map is My_Hash.Map
     (Capacity => Capacity,
      Modulus  => Modulus);

   type My_Mapping is record
      X : My_Hash_Map;
   end record;

end P;
