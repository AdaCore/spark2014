pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);
package Nested_Prot with SPARK_Mode is
   protected type P1 is
      function Get return Integer;
      procedure Set (X : Integer);
      entry Reset;
   private
      C : Integer := 0;
   end P1;
   protected type P2 is
      function Get return Integer;
      procedure Set (X : Integer);
      procedure Reset;
   private
      C : P1;
   end P2;
end Nested_Prot;
