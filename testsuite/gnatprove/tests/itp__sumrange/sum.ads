

package Sum with SPARK_Mode is

   subtype Index is Integer range 0 .. 300;

   subtype Bounded_Integer is Integer range -2000 .. 2000;

   type Arr is array (Index) of Bounded_Integer;

   function Sum (A : Arr; I, J : Index) return Integer is
      (if J <= I then
         0
      else
         (A (I) + Sum (A, I + 1, J)))
   With
   Pre => I <= J,
   Post => abs (Sum'Result) <= (J - I) * 3000;

--      with Ghost,
--     Pre => I <= J,
--    Post => abs (Sum'Result) <= (J - I) * 3000 and then
--       (if I < J then Sum'Result = A (I) + Sum (A, I + 1, J)
--                            else Sum'Result = 0);
   pragma Annotate (GNATprove, Terminating, Sum);

--     procedure Sum_Axiom (A : Arr) with
--       Ghost,
--       Post => (for all I in Index =>
--                  (for all J in Index =>
--                       (if I < J then Sum (A, I, J) = A (I) + Sum (A, I + 1, J)
--                              else Sum (A, I, J) = 0)));

   function Simple_Sum (A : Arr; I, J : Index) return Integer with
     Pre => I <= J,
     Post => Simple_Sum'Result = Sum (A, I, J);



end Sum;
