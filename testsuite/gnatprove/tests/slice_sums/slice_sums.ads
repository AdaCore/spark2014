with Sums; use Sums;

package Slice_Sums is

   function Maximal_Sum_Slice_Bounds (X : Vector) return Slice_Bounds with
     Post => (if Maximal_Sum_Slice_Bounds'Result.Lo  <=
                Maximal_Sum_Slice_Bounds'Result.Hi then
                  (X'First <= Maximal_Sum_Slice_Bounds'Result.Lo and then
                       Maximal_Sum_Slice_Bounds'Result.Hi <= X'Last and then
                     (for all Lo in Index range X'First .. X'Last =>
                        (for all Hi in Index range X'First .. X'Last =>
                             (Sum (X, Maximal_Sum_Slice_Bounds'Result) >=
                                    Sum (X, Slice_Bounds'(Lo, Hi))))) and then
                     (Sum (X, Maximal_Sum_Slice_Bounds'Result) >= 0)));

    function Maximal_Sum_Slice_Bounds_2 (X : Vector) return Slice_Bounds with
     Post => (if Maximal_Sum_Slice_Bounds_2'Result.Lo  <=
                Maximal_Sum_Slice_Bounds_2'Result.Hi then
                  (X'First <= Maximal_Sum_Slice_Bounds_2'Result.Lo and then
                       Maximal_Sum_Slice_Bounds_2'Result.Hi <= X'Last and then
                     (for all Lo in Index range X'First .. X'Last =>
                        (for all Hi in Index range X'First .. X'Last =>
                             (Sum (X, Maximal_Sum_Slice_Bounds_2'Result) >=
                                    Sum (X, Slice_Bounds'(Lo, Hi))))) and then
                     (Sum (X, Maximal_Sum_Slice_Bounds_2'Result) >= 0)));

end Slice_Sums;
