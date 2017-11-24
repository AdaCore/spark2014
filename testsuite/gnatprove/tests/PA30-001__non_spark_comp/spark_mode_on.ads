pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
with SPARK_Mode_Auto;

package SPARK_Mode_On with SPARK_Mode is

   protected type My_Prot is
      function Get_X return Integer;
      function Get_Y return Integer;
      function Get_Z return Integer;
      procedure Set_X (V : Integer);
      procedure Set_Y (V : Integer);
      procedure Set_Z (V : Integer);
   private
      pragma SPARK_Mode (Off);
      X : SPARK_Mode_Auto.Bad;
      Y : Integer := 0;
      Z : Integer;
   end My_Prot;

   P : My_Prot;

   protected S is
      function Get_X return Integer;
      function Get_Y return Integer;
      function Get_Z return Integer;
      procedure Set_X (V : Integer);
      procedure Set_Y (V : Integer);
      procedure Set_Z (V : Integer);
   private
      Y : Integer := 0;
   end S;

   protected S2 is
      function Get_X return Integer;
      function Get_Y return Integer;
      function Get_Z return Integer;
      procedure Set_X (V : Integer);
      procedure Set_Y (V : Integer);
      procedure Set_Z (V : Integer);
   private
      pragma SPARK_Mode (Off);
      X : SPARK_Mode_Auto.Bad;
   end S2;

   Z : Integer := 0 with Part_Of => S;
   Z2 : Integer := 0 with Part_Of => S2;

private
   pragma SPARK_Mode (Off);
   X : SPARK_Mode_Auto.Bad with Part_Of => S;
   Y2 : Integer := 0 with Part_Of => S2;
end SPARK_Mode_On;
