
procedure Test_Traversal with SPARK_Mode is
   type Int_Acc is not null access Integer;
   type R is record
      F : Int_Acc;
   end record;

   function Get_F (X : not null access R) return not null access Integer is (X.F);

   procedure Use_Get_F_1 (X : not null access R) with
     Global => null,
     Pre => X.F.all = 23
   is
   begin
      pragma Assert (Get_F (X).all = 23); -- @ASSERT:PASS
   end Use_Get_F_1;

   procedure Use_Get_F_2 (X : not null access R) with
     Global => null,
     Pre  => X.F.all = 23,
     Post => X.F.all = 32 -- @POSTCONDITION:PASS
   is
      B : access Integer := Get_F (X);
   begin
      B.all := 32;
   end Use_Get_F_2;

   procedure Use_Get_F_3 (X : not null access R) with
     Global => null,
     Pre => X.F.all = 23
   is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Get_F);
   begin
      pragma Assert (Get_F (X).all = 23); -- @ASSERT:FAIL
   end Use_Get_F_3;

   procedure Use_Get_F_4 (X : not null access R) with
     Global => null,
     Pre  => X.F.all = 23,
     Post => X.F.all = 32 -- @POSTCONDITION:FAIL
   is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Get_F);
      B : access Integer := Get_F (X);
   begin
      B.all := 32;
   end Use_Get_F_4;
begin
   null;
end Test_Traversal;
