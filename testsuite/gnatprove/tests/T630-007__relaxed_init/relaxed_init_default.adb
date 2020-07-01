procedure Relaxed_Init_Default with SPARK_Mode is
   type My_Int is new Integer with Default_Value => 0;
   X : My_Int with Relaxed_Initialization;

   function Id (X : Integer) return Integer is (X);

   type My_Arr is array (Positive range <>) of Integer with Default_Component_Value => 0;
   A : My_Arr (1 .. Id (5)) with Relaxed_Initialization;
   B : My_Arr (1 .. 5) := (others => 1) with Relaxed_Initialization;

   procedure Do_Something with Global => (Output => A), Import;

   type My_Rec is record
      F, G : Integer;
   end record;

   type A_Rec is array (Positive range <>) of My_Rec;
   R1 : My_Rec with Relaxed_Initialization;
   R2 : My_Rec := (1, 2);
   AR : A_Rec (1 .. 2) := (R1, R2) with Relaxed_Initialization;

   type My_Bool is new Boolean with Relaxed_Initialization;
   type Bool_Arr is array (Positive range 1 .. 5) of My_Bool;
   AB : Bool_Arr := (others => True);
begin
   pragma Assert (X'Initialized);
   pragma Assert (A'Initialized);
   pragma Assert (A /= B);
   pragma Assert (A < B);
   B := (1 .. 3 => 0) & A (1 .. 2);
   pragma Assert (B'Initialized);
   B := A (1 .. 2) & (1 .. 3 => 0);
   pragma Assert (B'Initialized);
   pragma Assert (AR (2)'Initialized);
   AR := AR (2 .. 2) & R2;
   pragma Assert (AR'Initialized);
   AR := R2 & AR (2 .. 2);
   pragma Assert (AR'Initialized);
   AR := AR (2 .. 2) & R1;
   pragma Assert (AR (1)'Initialized);
   AR := R1 & AR (1 .. 1);
   pragma Assert (AR (2)'Initialized);
   AB := not AB;
   pragma Assert (AB'Initialized);
   Do_Something;
   pragma Assert (A'Initialized); --@ASSERT:FAIL
end Relaxed_Init_Default;
