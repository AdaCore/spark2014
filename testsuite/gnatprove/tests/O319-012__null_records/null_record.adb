package body Null_Record with Spark_Mode is
   procedure Check_Equal is
      O1 : Null_Rec;
      O2 : Null_Rec2;
      O3 : Null_Rec2 := O1;
      T1 : T_Null_Rec;
      T2 : T_Null_Rec2;
      T3 : T_Null_Rec := T_Null_Rec (T2);
   begin
      pragma Assert (O2 = O3);
      pragma Assert (T1 = T3);
   end Check_Equal;

   procedure Check_Aggregate is
      O1 : Null_Rec := Null_Rec'(null record);
      O2 : Null_Rec2 := (others => <>);
      T1 : T_Null_Rec := T_Null_Rec'(null record);
      T2 : T_Null_Rec2 := (others => <>);
      T3 : T_Null_Rec2 := (T1 with others => <>);
   begin
      null;
   end Check_Aggregate;

   procedure Do_Nothing1 (O : in out Null_Rec) with
     Pre => True
   is
   begin
      O := (others => <>);
   end Do_Nothing1;

   O : Null_Rec;

   procedure Do_Nothing2 with
     Pre => True
   is
   begin
      O := (others => <>);
   end Do_Nothing2;

   procedure T_Do_Nothing1 (T : in out T_Null_Rec) with
     Pre => True
   is
   begin
      T := (others => <>);
   end T_Do_Nothing1;

   T : T_Null_Rec;

   procedure T_Do_Nothing2 with
     Pre => True
   is
   begin
      T := (others => <>);
   end T_Do_Nothing2;

   procedure Check_Procedure_Call is
      O1 : Null_Rec;
      O2 : constant Null_Rec := O1;
      O3 : constant Null_Rec := O;
      T1 : T_Null_Rec;
      T2 : constant T_Null_Rec := T1;
      T3 : constant T_Null_Rec := T;
   begin
      Do_Nothing1 (O1);
      pragma Assert (O1 = O2);
      Do_Nothing2;
      pragma Assert (O = O3);
      T_Do_Nothing1 (T1);
      pragma Assert (T1 = T2);
      T_Do_Nothing2;
      pragma Assert (T = T3);
   end Check_Procedure_Call;
end Null_Record;
