procedure Test_Global_Out with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   function Rand return Boolean with Import;

   type Rec is record
      F, G : Integer;
   end record with
     Annotate => (GNATprove, Init_By_Proof);

   G : Rec;

   function Safe_Get_G return Integer is
     (if G.G'Valid_Scalars then G.G else 0);

   procedure Init_F_1 with
     Post => G.F'Valid_Scalars
     and G.G'Valid_Scalars = G.G'Valid_Scalars'Old
     and Safe_Get_G = Safe_Get_G'Old
   is
   begin
      G.F := 1;
   end Init_F_1;

   procedure Init_F_2 with
     Global => (In_Out => G),
     Post => G.F'Valid_Scalars
     and G.G'Valid_Scalars = G.G'Valid_Scalars'Old
     and Safe_Get_G = Safe_Get_G'Old
   is
   begin
      G.F := 1;
   end Init_F_2;

   procedure Init_F_3 with
     Global => (Output => G),
     Depends => (G => null),
     Post => G.F'Valid_Scalars
     and G.G'Valid_Scalars = G.G'Valid_Scalars'Old -- no flow checks should be emitted here
     and Safe_Get_G = Safe_Get_G'Old
   is
   begin
      G.F := 1;
   end Init_F_3;

   type My_Int is new Integer with Annotate => (GNATprove, Init_By_Proof);

   B : Boolean;
   I : My_Int;

   function Safe_Get_I return My_Int is
     (if I'Valid_Scalars then I else 0);

   procedure Init_Cond_1 with
     Post => (if B then I'Valid_Scalars
              else I'Valid_Scalars = I'Valid_Scalars'Old
              and Safe_Get_I = Safe_Get_I'Old)
   is
   begin
      if B then
         I := 1;
      end if;
   end Init_Cond_1;

   procedure Init_Cond_2 with
     Global => (In_Out => I, Input => B),
     Post => (if B then I'Valid_Scalars
              else I'Valid_Scalars = I'Valid_Scalars'Old
              and Safe_Get_I = Safe_Get_I'Old)
   is
   begin
      if B then
         I := 1;
      end if;
   end Init_Cond_2;

   procedure Init_Cond_3 with
     Global => (Output => I, Input => B),
     Post => (if B then I'Valid_Scalars
              else I'Valid_Scalars = I'Valid_Scalars'Old -- no flow checks should be emitted here
              and Safe_Get_I = Safe_Get_I'Old)
   is
   begin
      if B then
         I := 1;
      end if;
   end Init_Cond_3;
begin
   G.G := 1;
   Init_F_1;
   pragma Assert (G.G = 1);--@ASSERT:PASS
   Init_F_2;
   pragma Assert (G.G = 1);--@ASSERT:PASS
   Init_F_3;
   pragma Assert (G.G = 1); --@ASSERT:FAIL--@INIT_BY_PROOF:FAIL
   --  Reading G.G should not be allowed, or we would miss dependencies from G.G to its initial value

   B := Rand;
   if not B then
      I := 1;
   end if;
   Init_Cond_1;
   pragma Assert (if not B then I = 1);
   Init_Cond_2;
   pragma Assert (if not B then I = 1);
   Init_Cond_3;
   pragma Assert (if not B then I = 1); --@ASSERT:FAIL--@INIT_BY_PROOF:FAIL
end Test_Global_Out;
