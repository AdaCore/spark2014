pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);
package P is
   protected type PT is
      function F return Integer;

   private
      X : access Integer;
   end PT;

   protected PO2 is
      function Fun2 return Integer;
   end PO2;

   X : Integer with Part_Of => PO2;

   type T is record
      A : Integer;
      B : PT;
   end record;

   Ob  : T;

end P;
