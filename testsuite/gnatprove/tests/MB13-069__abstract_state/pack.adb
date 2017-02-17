pragma SPARK_Mode;

package body Pack with
  Refined_State => (Content => A)
is
   A : Integer := 0;

   procedure Update_Content with
     Refined_Global => (In_Out => A) is
   begin
      A := A + 1;
   end Update_Content;
end Pack;
