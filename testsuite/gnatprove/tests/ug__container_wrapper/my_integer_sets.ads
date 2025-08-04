with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Types; use SPARK.Containers.Types;
with SPARK.Containers.Formal.Hashed_Sets;
with SPARK.Containers.Functional.Sets;

package My_Integer_Sets with SPARK_Mode is
   type My_Int is range -100 .. 100;

   package Set_Models is new SPARK.Containers.Functional.Sets (My_Int);
   use all type Set_Models.Set;

   type Set is private with
     Default_Initial_Condition => Cardinality (Set) = 0;

   function Model (X : Set) return Set_Models.Set with Ghost;

   function Cardinality (X : Set) return Natural with
     Post => To_Big_Integer (Cardinality'Result) = Length (Model (X));

   function Contains (X : Set; Y : My_Int) return Boolean with
     Post => Contains'Result = Contains (Model (X), Y);

   procedure Add (X : in out Set; Y : My_Int) with
     Contract_Cases =>
       (Contains (X, Y) => Model (X) = Model (X)'Old,
        others          => Model (X) = Add (Model (X)'Old, Y));

private
   function Hash (X : My_Int) return Hash_Type is
     (Hash_Type (100 + Integer (X)));
   package Inst is new SPARK.Containers.Formal.Hashed_Sets (My_Int, Hash);
   type Set is record
      Impl : Inst.Set (201, Inst.Default_Modulus (201));
   end record;
   --  Use a big enough value to hold all elements of My_Int in a set
end;
