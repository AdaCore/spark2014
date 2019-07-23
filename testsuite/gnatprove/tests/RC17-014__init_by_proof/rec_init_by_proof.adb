with Ada.Text_IO;
procedure Rec_Init_By_Proof with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   subtype My_Nat is Integer range 10 .. 150;
   pragma Annotate (GNATprove, Init_By_Proof, My_Nat);

   type Three_Fields is record
      F1 : My_Nat;
      F2 : My_Nat;
      F3 : My_Nat := 12;
   end record;

   procedure Init_F1 (X : in out Three_Fields) with
     Post => X.F1'Valid_Scalars
     and then X.F2'Valid_Scalars = X.F2'Valid_Scalars'Old
     and then X.F3'Valid_Scalars = X.F3'Valid_Scalars'Old
     and then X.F1 = 20
     and then (if X.F2'Valid_Scalars then X.F2 = X'Old.F2)
     and then (if X.F3'Valid_Scalars then X.F3 = X'Old.F3)
   is
   begin
      X.F1 := 20;
   end Init_F1;

   procedure Init_F2 (X : in out Three_Fields) with
     Post => X.F2'Valid_Scalars
     and then X.F1'Valid_Scalars = X.F1'Valid_Scalars'Old
     and then X.F3'Valid_Scalars = X.F3'Valid_Scalars'Old
     and then X.F2 = 30
     and then (if X.F1'Valid_Scalars then X.F1 = X'Old.F1)
     and then (if X.F3'Valid_Scalars then X.F3 = X'Old.F3)
   is
   begin
      X.F2 := 30;
   end Init_F2;

   procedure Process (X : in out Three_Fields) with
     Pre  => X'Valid_Scalars,
     Post => X'Valid_Scalars
   is
   begin
      X.F1 := X.F1 / 2 + 5;
      X.F2 := X.F2 / 2 + 5;
      X.F3 := X.F3 / 2 + 5;
   end Process;

   procedure Do_Nothing (X : out Three_Fields) with
     Pre => X'Valid_Scalars
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
