pragma SPARK_Mode;

package Noc is
   type Value_Type is new Integer;

   type Atomic_Type is new Value_Type with Volatile, No_Caching;

   procedure Store(Loc : aliased out Atomic_Type; V : Value_Type) is null;

   MyAtomicVar : aliased Atomic_Type;

   type Rec is record
      X : Integer;
      Y : Atomic_Type;
   end record;

   MyRec : Rec;

   function Get (R : Rec) return Integer is (R.X);

   type Rec2 is record
      X : Integer;
      Y : Atomic_Type;
   end record with Volatile, No_Caching;

   MyRec2 : Rec2;

   function Get (R : Rec2) return Integer is (R.X);

   type Arr is array(Atomic_Type range <>) of Rec;

   A : Arr(1 .. 42) := (others => (1, 2));

   pragma Assert
     (for all I in Integer(A'First) .. Integer(A'Last) =>
        A(Atomic_Type(I)) = (1, 2));

   type Arr2 is array(Atomic_Type range <>) of Rec
     with Volatile, No_Caching;

   A2 : Arr2(1 .. 42) := (others => (1, 2));

   pragma Assert
     (for all I in Integer(A2'First) .. Integer(A2'Last) =>
        A2(Atomic_Type(I)) = (1, 2));

   procedure Test;

end Noc;
