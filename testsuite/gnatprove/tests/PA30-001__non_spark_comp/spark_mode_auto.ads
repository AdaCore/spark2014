pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package SPARK_Mode_Auto is
   type Bad is access all Integer;

   protected type My_Prot is
      function Get_X return Integer;
      function Get_Y return Integer;
      function Get_Z return Integer;
      procedure Set_X (V : Integer);
      procedure Set_Y (V : Integer);
      procedure Set_Z (V : Integer);
   private
      X : Bad;
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
      X : Bad;
   end S2;

   X : Bad with Part_Of => S;
   Z : Integer := 0 with Part_Of => S;
   Y2 : Integer := 0 with Part_Of => S2;
   Z2 : Integer := 0 with Part_Of => S2;

end SPARK_Mode_Auto;
