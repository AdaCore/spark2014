generic
   Max : Integer;
package Other
  with SPARK_Mode
is
   Visible_Var : Integer := 0;

   function Foo return Integer;
private
   pragma SPARK_Mode (Off);
   Private_Var : Integer := 0;
end Other;
