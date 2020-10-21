package Predicates
  with SPARK_Mode
is
   subtype Count is Integer with
     Static_Predicate => Count /= 10 and Count /= 100;

   subtype Count2 is Integer with
     Static_Predicate => Count2 in Integer'First .. 9 | 11 .. 99 | 101 .. Integer'Last;

   type Count3 is new Natural with
     Static_Predicate => Count3 /= 10 and Count3 /= 100;

   subtype Normal_Float is Float with
     Static_Predicate => Normal_Float <= -2.0**(-126) or Normal_Float = 0.0 or Normal_Float >= 2.0**(-126);

   subtype Odd is Natural with
     Dynamic_Predicate => Odd mod 2 = 1;

   subtype Even is Natural with
     Dynamic_Predicate => Even mod 2 = 0;

   type Prime is new Positive with
     Dynamic_Predicate => (for all Divisor in 2 .. Prime / 2 => Prime mod Divisor /= 0);

   type Distinct_Pair is record
     Val1, Val2 : Integer;
   end record
     with Dynamic_Predicate => Distinct_Pair.Val1 /= Distinct_Pair.Val2;

   function Get_GCD (X, Y : Integer) return Natural is
      (if X < 0 or Y < 0 then
         Get_GCD (abs (X), abs (Y))
       elsif X = 0 or Y = 0 then
         Integer'Max (X, Y)
       elsif X >= Y then
         Get_GCD (Y, X - Y)
       else
         Get_GCD (X, Y - X));

   type Bundle_Values is record
     X, Y : Integer;
     GCD  : Natural;
   end record
     with Dynamic_Predicate => Bundle_Values.GCD = Get_GCD (Bundle_Values.X, Bundle_Values.Y);

   type Data_Array is array (Positive range <>) of Integer;

   type Resizable_Table (Max : Natural) is record
      Count : Natural;
      Data  : Data_Array(1 .. Max);
   end record
     with Dynamic_Predicate => Resizable_Table.Count <= Resizable_Table.Max;

   type Index is range 1 .. 10;

   type Ordered_Array is array (Index) of Integer
     with Dynamic_Predicate =>
       (for all I in Index => (if I < Index'Last then Ordered_Array(I) < Ordered_Array(I+1)));

   End_Marker : constant := -1;

   type Ended_Array is array (Index) of Integer
     with Dynamic_Predicate =>
       (for some I in Index => Ended_Array(I) = End_Marker);

end Predicates;
