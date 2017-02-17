package Sub is pragma SPARK_Mode (On);

   type My_Int is range 0 .. 1000;

   Global : My_Int := 0;

   subtype S is My_Int
      with Dynamic_Predicate => S mod 2 = 0;
   -- all elements of S are even

   subtype T is My_Int
   with Dynamic_Predicate => (Global + T) mod 2 = 0;
   -- the predicate of T depends on a global variable

   --  All of these subprograms want to divide their argument X by 2 at some
   --  point, which may break the subtype predicate.

   function Incorrect (X : S) return S;

   function F (X : S) return S;

   procedure Divide (X : in out S);

   procedure Divide_T (X : in out T);

end Sub;
