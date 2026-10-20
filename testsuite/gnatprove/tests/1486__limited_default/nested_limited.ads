pragma Ada_2022;
package nested_limited with SPARK_Mode is
   type State (A, B, C : Positive) is limited private;
   function Fresh (A, B, C : Positive) return State with
     Post => Fresh'Result.A = A and then Fresh'Result.B = B and then Fresh'Result.C = C;
private
   type Inner is limited record X : Natural := 0; end record;
   type State (A, B, C : Positive) is limited record
      Value : Inner;
   end record;
end nested_limited;
