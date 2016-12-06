package body My_Types with SPARK_Mode is
   protected body Prot is
      function Get_F return Integer is (F);
      procedure Set_F (V : Integer) is
      begin
         F := V;
      end Set_F;
   end Prot;

   procedure Use_P_2 is
      X : Integer;
   begin
      X := P_2.Get_F;
      P_2.Set_F (X + 1);
   end Use_P_2;

   procedure Use_P_3 is
      X : Integer;
   begin
      X := P_3.Get_F;
      P_3.Set_F (X + 1);
   end Use_P_3;

   procedure Use_P_4 is
      X : Integer;
   begin
      X := P_4.Get_F;
      P_4.Set_F (X + 1);
   end Use_P_4;
end My_Types;
