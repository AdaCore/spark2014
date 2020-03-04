procedure Test_Init_By_Proof with SPARK_Mode is
   type My_Int is new Integer;
   pragma Annotate (GNATProve, Init_By_Proof, My_Int);
   type Rec is record
      X : Integer;
      Y : My_Int;
      Z : Boolean;
   end record;
   type Rec_2 is new Rec;
   pragma Annotate (GNATProve, Init_By_Proof, Rec_2);
   type Holder is record
      F : Rec;
      G : Rec_2;
   end record;
   type Rec_3 (D : My_Int) is record
      Y : My_Int;
      case D is
      when 0 =>
         X : Integer;
      when others => null;
      end case;
   end record;
   pragma Annotate (GNATProve, Init_By_Proof, Rec_3);

   procedure Test_Discr (X : Rec_3) with
     Pre => X'Valid_Scalars and then X.D = 0
   is
      Y : Integer := X.X + Integer (X.D); --@INIT_BY_PROOF:PASS
      Z : My_Int := X.Y + X.D; --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test_Discr;

   procedure Test_Discr_2 (X : Rec_3) with
     Pre => X.D = 0
   is
      Y : Integer := X.X + Integer (X.D); --@INIT_BY_PROOF:FAIL
      Z : My_Int := X.Y + X.D; --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test_Discr_2;

   procedure Test_Init_Attr (X : Rec; Y : Rec_2) with
     Pre => X.Y'Valid_Scalars and Y'Valid_Scalars
   is
   begin
      pragma Assert (Holder'(X, Y)'Valid_Scalars);--@ASSERT:PASS
   end Test_Init_Attr;

   procedure Test_Init_Attr_2 (X : Rec; Y : Rec_2) with
     Pre => X.Y'Valid_Scalars or Y'Valid_Scalars
   is
   begin
      pragma Assert (Holder'(X, Y)'Valid_Scalars);--@ASSERT:FAIL
   end Test_Init_Attr_2;

   procedure P1 is
      X1 : Rec_2 := (1, 2, True);
      Y1 : Integer := X1.X; --@INIT_BY_PROOF:PASS
      Z1 : My_Int := X1.Y; --@INIT_BY_PROOF:PASS
      W1 : Boolean := X1.Z; --@INIT_BY_PROOF:PASS
   begin
      null;
   end;
   procedure P2 is
      X2 : Rec_2;
      Y2 : Integer := X2.X; --@INIT_BY_PROOF:FAIL
      Z2 : My_Int := X2.Y; --@INIT_BY_PROOF:FAIL
      W2 : Boolean := X2.Z; --@INIT_BY_PROOF:FAIL
   begin
      null;
   end;
   procedure P3 is
      X1 : Rec := (1, 2, True);
      Y1 : Integer := X1.X; --@INIT_BY_PROOF:NONE
      Z1 : My_Int := X1.Y; --@INIT_BY_PROOF:PASS
   begin
      null;
   end;
   procedure P4 is
      X2 : Rec;
      Y2 : Integer := X2.X; --@INIT_BY_PROOF:NONE
      Z2 : My_Int := X2.Y; --@INIT_BY_PROOF:FAIL
   begin
      null;
   end;
   procedure P5 is
      X2 : Rec_2;
      Y2 : Integer;
      Z2 : My_Int;
   begin
      X2.X := 1;
      Y2 := X2.X; --@INIT_BY_PROOF:PASS
      Z2 := X2.Y; --@INIT_BY_PROOF:FAIL
   end;
   procedure P6 is
      X2 : Rec;
      Y2 : Integer;
      Z2 : My_Int;
   begin
      X2.X := 1;
      Y2 := X2.X; --@INIT_BY_PROOF:NONE
      Z2 := X2.Y; --@INIT_BY_PROOF:FAIL
   end;
   procedure P7 is
      X2 : Rec_2;
      Y2 : Integer;
      Z2 : My_Int;
   begin
      X2.Y := 1;
      Y2 := X2.X; --@INIT_BY_PROOF:FAIL
      Z2 := X2.Y; --@INIT_BY_PROOF:PASS
   end;
   procedure P8 is
      X2 : Rec;
      Y2 : Integer;
      Z2 : My_Int;
   begin
      X2.Y := 1;
      Y2 := X2.X; --@INIT_BY_PROOF:NONE
      Z2 := X2.Y; --@INIT_BY_PROOF:PASS
   end;
   procedure P9 is
      X : Rec_2;
      X2 : Rec := Rec (X); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end;
   procedure P10 is
      X : Rec_2;
      X2 : Rec;
   begin
      X.X := 15;
      X.Z := True;
      X2 := Rec (X); --@INIT_BY_PROOF:PASS
   end;
   procedure Q is
      X : Holder;
   begin
      X.G.Y := 15;
      X.G.Z := True;
      X.F := Rec (X.G); --@INIT_BY_PROOF:FAIL
   end;
   procedure Q1 is
      X : Holder;
   begin
      X.G.X := 15;
      X.G.Z := True;
      X.F := Rec (X.G); --@INIT_BY_PROOF:PASS
   end;
begin
   null;
end Test_Init_By_Proof;
