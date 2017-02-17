package Simple_Unc_Arrays is pragma SPARK_Mode (On);

  -- This should be a generic parameter
   type Value is new Integer; -- should be range <>;

   -- This is declaring arrays with a fixed first bound of 1

   type Values is array (Positive range <>) of Value;

   type Table (Last : Natural) is record
      V : Values (1 .. Last);
   end record;

   ---------
   -- Add --
   ---------

   function Add (A, B : Table) return Table
   with Pre  => Same_Range (A, B),
   Post => (Same_Range (Add'Result, A)
            and then (for all J in 1 .. A.Last =>
                        (Add'Result.V (J) = A.V (J) + B.V (J))));

   -------------
   -- Reverse --
   -------------

   Procedure Inverse (A : in out Table)
   with Post => (for all J in 1 .. A.Last =>
                   (A.V (J) = A.V'Old (A.Last - J + 1)));
   --  Reverses the content of A

   ---------
   -- Min --
   ---------

   function Min (A : Table) return Value
   with
     Pre => not Empty (A),
     Post => (for all  J in 1 .. A.Last => (Min'Result <= A.V (J)))
            and then
              (for some J in 1 .. A.Last => (Min'Result  = A.V (J)));
   --  Returns the minimum value occurring in A

   ---------
   -- Max --
   ---------

   function Max (A : Table) return Value
   with
     Pre  => not Empty (A),
     Post =>  (for all  J in 1 .. A.Last => (Max'Result >= A.V(J)))
               and then
                 (for some J in 1 .. A.Last => (Max'Result  = A.V (J)));
   --  Returns the maximun value occurring in A

   -------------
   -- Average --
   -------------

   function Average (A : Table) return Value
   with
     Pre  => not Empty (A),
     Post => Min (A) <= Average'Result
     and then Max (A) >= Average'Result;
   --  Returns the average value in A. Here, the given postcondition does not
   --  describe completely the value returned.

   ------------
   -- Search --
   ------------

   function Search (A : Table; V : Value) return Natural
   with Post => (Search'Result = 0 and then Not_In (A, V, 1 ,A.Last))
     or else (A.V (Search'Result) = V
              and then Not_In (A, V, 1, Search'Result-1));
   --  Returns the first index at which value V occurs in array A, or else 0

   -----------------
   -- Bubble_Sort --
   -----------------

   function Bubble_Sort (A: Table) return Table
   with Post => (for all J in 1 ..  A.Last - 1 =>
               Bubble_Sort'Result.V (J) <= Bubble_Sort'Result.V (J+1))
     and then (for all J in 1 .. A.Last =>
                  (for some K in 1 .. A.Last =>
                    A.V (J) = Bubble_Sort'Result.V (K)));
   --  Sorts an array in increasing order by using bubble sort

   ----------------
   -- Quick_Sort --
   ----------------

   Procedure Quick_Sort (A: in out Table)
   with Post => (for all J in 1 ..  A.Last - 1 => A.V (J) <= A.V (J+1))
     and then (for all J in 1 .. A.Last =>
               (for some K in 1 .. A.Last => A.V'Old (J) = A.V (K)));
   --  Sorts an array in increasing order by using quick sort

   -----------------
   -- utilities --
   -----------------

   function Empty (A : Table) return Boolean is (1 > A.Last);
   function Same_Range (A, B : Table) return Boolean is (A.Last = B.Last);
   function Not_In  (A   : Table;
                     V   : Value;
                     Low : Positive;
                     Up  : Natural)
     return Boolean is
       (Up > A.Last or else (for all J in Low .. Up => A.V (J) /= V));


   procedure Swap (V, W : in out Value)
   with Post => (V = W'Old and then W = V'Old);
   --  Swaps two values V and W

   procedure Swap_Cells (A : in out Values; I, J : Positive)
      with Pre  => I in A'Range and J in A'Range,
           Post => (A (I) = A'Old (J) and A (J) = A'Old (I) and
                     (for all K in A'Range =>
                        (if K /= I and K /= J then A (K) = A'Old (K))));
   --  Swaps two values V and W
   --
   procedure Output (S : String; I : Value);

end Simple_Unc_Arrays;
