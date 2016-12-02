package body SPARK_Mode_Auto is

   protected body My_Prot is
      function Get_X return Integer is (X.all);
      function Get_Y return Integer is (Y);
      function Get_Z return Integer is (Z);
      procedure Set_X (V : Integer) is
      begin
         X.all := V;
      end Set_X;
      procedure Set_Y (V : Integer) is
      begin
         Y := V;
      end Set_Y;
      procedure Set_Z (V : Integer)is
      begin
         Z := V;
      end Set_Z;
   end My_Prot;

   protected body S is
      function Get_X return Integer is (X.all);
      function Get_Y return Integer is (Y);
      function Get_Z return Integer is (Z);
      procedure Set_X (V : Integer) is
      begin
         X.all := V;
      end Set_X;
      procedure Set_Y (V : Integer) is
      begin
         Y := V;
      end Set_Y;
      procedure Set_Z (V : Integer)is
      begin
         Z := V;
      end Set_Z;
   end S;

   protected body S2 is
      function Get_X return Integer is (X.all);
      function Get_Y return Integer is (Y);
      function Get_Z return Integer is (Z);
      procedure Set_X (V : Integer) is
      begin
         X.all := V;
      end Set_X;
      procedure Set_Y (V : Integer) is
      begin
         Y := V;
      end Set_Y;
      procedure Set_Z (V : Integer)is
      begin
         Z := V;
      end Set_Z;
   end S2;
end SPARK_Mode_Auto;
