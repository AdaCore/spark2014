pragma SPARK_Mode;

package body Pack with
  Refined_State => (Content => (A, B))
is
   A, B : Integer := 0;

   procedure Update_Content with
     Refined_Global => (In_Out => A) is
   begin
      A := A + B;
   end Update_Content;
end Pack;
