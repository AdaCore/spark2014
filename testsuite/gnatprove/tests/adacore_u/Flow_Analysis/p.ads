package P with SPARK_Mode is
   type Array_Of_Positives is array (Integer range <>) of Positive;

   procedure Search_Array (A      :     Array_Of_Positives;
                           E      :     Positive;
                           Result : out Integer;
                           Found  : out Boolean);

   type Search_Result (Found : Boolean := False) is record
      case Found is
         when True =>
            Content : Integer;
         when False =>
            null;
      end case;
   end record;

   procedure Search_Array (A      :     Array_Of_Positives;
                           E      :     Positive;
                           Result : out Search_Result) with
     Pre => not Result'Constrained;

   procedure Search_Array (A      :     Array_Of_Positives;
                           E      :     Positive;
                           Result : out Integer) with
     Pre => (for some I in A'Range => A (I) = E);

   procedure Incr_Step_Function (A : in out Array_Of_Positives);

   function Size_Of_Biggest_Increasing_Sequence
     (A : Array_Of_Positives) return Natural;

   type Permutation is array (Positive range <>) of Positive;

   procedure Init (A : out Permutation);

   procedure Swap (A : in out Permutation; X, Y : Positive) with
     Pre => X in A'Range and then Y in A'Range and then X /= Y;

   function Cyclic_Permutation (N : Natural) return Permutation;

   procedure Swap (X, Y : in out Positive) with
     Depends => (X => Y,
                 Y => X);

   procedure Identity (X, Y : in out Positive) with
     Depends => (X => X,
                 Y => Y);

end P;
