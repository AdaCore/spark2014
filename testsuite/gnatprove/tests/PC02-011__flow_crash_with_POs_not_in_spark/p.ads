pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package P is
   protected type PT is
      function Fun return Integer;
   private
      X : Integer := 0;
   end PT;

   PO : PT;

   protected PO2 is
      function Fun2 return Integer;
   end PO2;

   X : Integer with Part_Of => PO2;

end P;
