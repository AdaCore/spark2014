package Data_Structure
  with SPARK_Mode
is
   type Hash_Type is mod 2**32;
   type Count_Type is range 0 .. 2**31 - 1;
   subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
   subtype Positive_Hash_Type is Hash_Type range 1 .. Hash_Type'Last;

   type Element_Type is new Integer;
   function Equivalent_Elements (X, Y : Element_Type) return Boolean
   with Global => null, Import;
   function Hash (X : Element_Type) return Hash_Type
   with Global => null, Import;
   procedure Lemma_Equivalent_Elements_Refexive (X : Element_Type)
   with
     Global => null,
     Always_Terminates,
     Import,
     Ghost,
     Post   => Equivalent_Elements (X, X);
   procedure Lemma_Equivalent_Elements_Symmetric (X, Y : Element_Type)
   with
     Global => null,
     Always_Terminates,
     Import,
     Ghost,
     Post   => Equivalent_Elements (X, Y) = Equivalent_Elements (Y, X);
   procedure Lemma_Equivalent_Elements_Transitive (X, Y, Z : Element_Type)
   with
     Global => null,
     Always_Terminates,
     Import,
     Ghost,
     Post   =>
       (if Equivalent_Elements (X, Y) and Equivalent_Elements (Y, Z)
        then Equivalent_Elements (X, Z));
   procedure Lemma_Equivalent_Elements_Hash (X, Y : Element_Type)
   with
     Global => null,
     Always_Terminates,
     Import,
     Ghost,
     Post   => (if Equivalent_Elements (X, Y) then Hash (X) = Hash (Y));

   type Set
     (Capacity : Count_Type;
      Modulus  : Positive_Hash_Type)
   is
     private;

   function Find_Bucket (X : Element_Type; Modulus : Hash_Type) return Hash_Type
   with Pre => Modulus /= 0, Post => Find_Bucket'Result in 1 .. Modulus;

   procedure Lemma_Equivalent_Elements_Find_Bucket
     (X, Y : Element_Type; Modulus : Hash_Type)
   with
     Ghost,
     Pre  => Modulus /= 0,
     Post =>
       (if Equivalent_Elements (X, Y)
        then Find_Bucket (X, Modulus) = Find_Bucket (Y, Modulus));

private

   type Relaxed_Element is record
      V : Element_Type;
   end record
   with Relaxed_Initialization;

   type Memory_Cell is record
      Value       : Relaxed_Element;
      Next        : Count_Type := 0;
      Has_Element : Boolean := False;
   end record;

   type Memory_Type is array (Count_Type range 1.. <>) of Memory_Cell
   with
     Predicate =>
       Memory_Type'Last >= 0
       and then (for all C of Memory_Type => C.Next <= Memory_Type'Last);
   type Bucket_Array is array (Hash_Type range 1.. <>) of Count_Type;
   type Set
     (Capacity : Count_Type;
      Modulus  : Positive_Hash_Type)
   is record
      Memory  : Memory_Type (1 .. Capacity);
      Buckets : Bucket_Array (1 .. Modulus) := (others => 0);
      Free    : Count_Type'Base := -Capacity;
      Length  : Count_Type := 0;
   end record
   with
     Predicate =>
       Length in 0 .. Capacity
       and then Free in -Capacity .. Capacity
       and then (for all B of Set.Buckets => B <= Capacity);

end Data_Structure;
