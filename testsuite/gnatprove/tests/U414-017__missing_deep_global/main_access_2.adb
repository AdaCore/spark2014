procedure Main_Access_2 with SPARK_Mode Is
   type Rec is record
      F1, F2 : aliased Integer;
   end record;
   type Rec_Acc is access Rec;
   V_2 : Rec_Acc := new Rec'(1, 2);
   V_3 : Rec_Acc := new Rec'(1, 2);
   V_4 : Rec_Acc := new Rec'(1, 2);
   procedure Acc_2 with Global => null is
      package B is
         V_B : constant Rec_Acc := V_2;
      end B;
   begin
      null;
   end Acc_2;
   procedure Acc_3 with Global => null is
      package B is
         function F return Boolean;
      end B;
      package body B is
         V_B : constant Rec := V_3.all;
         function F return Boolean is (True);
      end B;
   begin
      null;
   end Acc_3;
   procedure Acc_4 with Global => null is
      package B is
         function F return Boolean;
      end B;
      package body B is
         function F return Boolean is (True);
      begin
         declare
            V_B : Rec := V_4.all;
         begin
            V_B.F1 := 15;
         end;
      end B;
   begin
      null;
   end Acc_4;
begin
   null;
end Main_Access_2;
