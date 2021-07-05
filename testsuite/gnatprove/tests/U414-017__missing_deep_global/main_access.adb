procedure Main_Access with SPARK_Mode Is
   type Rec is record
      F1, F2 : aliased Integer;
   end record;
   type Rec_Acc is access Rec;
   V : Rec_Acc := new Rec'(1, 2);
   procedure Acc with Global => null is
      V_B : constant access Rec := V;
   begin
      null;
   end Acc;
begin
   null;
end Main_Access;
