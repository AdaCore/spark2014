package Dynamic_Ranges with SPARK_Mode is

   type Int_Array is array (Positive range <>) of Integer;

   type Constr_Int_Array is new Int_Array (1 .. 100);

   C : Positive := 100;

   type Dyn_Int_Array is new Int_Array (1 .. C);

   function Resize (A : Int_Array) return Dyn_Int_Array with
     Pre => A'First <= 1 and then A'Last >= Dyn_Int_Array'Last;

   function Search (A : Int_Array; E : Integer) return Natural with
     Post => Search'Result = 0 or else
     (Search'Result in A'Range
      and then A (Search'Result) = E);

   function Search_0 (A : Int_Array) return Natural with
     Pre => A'Last >= A'First and then A'Last - A'First >= 2,
     Post => (Search_0'Result = 0
              and then (for all I in A'Range => A (I) /= 0))
     or else (Search_0'Result in A'Range and then A (Search_0'Result) = 0);

   procedure Store_Zero (A : in out Int_Array; I : Positive) with
     Pre => I in A'Range,
     Post => A (I) = 0 and then
     (for all J in A'Range => (if I /= J then A (J) = A'Old (J)));

   procedure All_Zeros (A : in out Int_Array) with
     Post => (for all J in A'Range => A (J) = 0);

end Dynamic_Ranges;
