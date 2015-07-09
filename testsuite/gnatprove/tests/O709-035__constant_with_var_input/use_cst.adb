with Cst; use Cst;
package body Use_Cst
  with SPARK_Mode
is
   procedure P is
      function Local return Integer with Pre => True;
      function Local return Integer is
      begin
         return Get_Y;
      end Local;
      X : Integer;
   begin
      X := Local;
   end P;
end Use_Cst;
