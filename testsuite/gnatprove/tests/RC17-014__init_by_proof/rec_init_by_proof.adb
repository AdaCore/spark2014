with Ada.Text_IO;
procedure Rec_Init_By_Proof with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   subtype My_Nat is Integer range 10 .. 150;

   type Three_Fields is record
      F1 : My_Nat;
      F2 : My_Nat;
      F3 : My_Nat := 12;
   end record with
     Relaxed_Initialization;

   procedure Init_F1 (X : in out Three_Fields) with
     Post => X.F1'Initialized
     and then X.F2'Initialized = X.F2'Initialized'Old
     and then X.F3'Initialized = X.F3'Initialized'Old
     and then X.F1 = 20
     and then (if X.F2'Initialized then X.F2 = X'Old.F2)
     and then (if X.F3'Initialized then X.F3 = X'Old.F3)
   is
   begin
      X.F1 := 20;
   end Init_F1;

   procedure Init_F2 (X : in out Three_Fields) with
     Post => X.F2'Initialized
     and then X.F1'Initialized = X.F1'Initialized'Old
     and then X.F3'Initialized = X.F3'Initialized'Old
     and then X.F2 = 30
     and then (if X.F1'Initialized then X.F1 = X'Old.F1)
     and then (if X.F3'Initialized then X.F3 = X'Old.F3)
   is
   begin
      X.F2 := 30;
   end Init_F2;

   procedure Process (X : in out Three_Fields) with
     Pre  => X'Initialized,
     Post => X'Initialized
   is
   begin
      X.F1 := X.F1 / 2 + 5;
      X.F2 := X.F2 / 2 + 5;
      X.F3 := X.F3 / 2 + 5;
   end Process;

   procedure Do_Nothing (X : out Three_Fields) with
     Pre => X'Initialized
   is
   begin
      null;
   end Do_Nothing;

   X : Three_Fields;
   Y : Three_Fields := (20, 30, 12);
   Z : Three_Fields;
   C : Integer;
   D : constant My_Nat := X.F3;
begin
   Init_F1 (X);
   Init_F2 (X);
   pragma Assert (X = Y);
   Process (X);
   Process (Y);
   Init_F1 (Z);
   Do_Nothing (X); --@PRECONDITION:FAIL
   C := Z.F2; -- @INIT_BY_PROOF:FAIL
end Rec_Init_By_Proof;
