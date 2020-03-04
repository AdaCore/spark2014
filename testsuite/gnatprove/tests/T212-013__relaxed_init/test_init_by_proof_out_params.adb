procedure Test_Init_By_Proof_Out_Params with SPARK_Mode is
   function Branch (X : Integer) return Boolean with
     Import;

   type My_Int is new Integer;
   pragma Annotate (GNATProve, Init_By_Proof, My_Int);
   type Rec is record
      X : Integer;
      Y : My_Int;
      Z : Boolean;
   end record;
   type Rec_2 is new Rec;
   pragma Annotate (GNATProve, Init_By_Proof, Rec_2);

   type Unc_Arr is array (My_Int range <>) of My_Int;
   type Unc_Arr_2 is array (My_Int range <>) of Integer;
   pragma Annotate (GNATProve, Init_By_Proof, Unc_Arr_2);

   type Constr_Arr is array (My_Int range 1 .. 10) of My_Int;
   type Constr_Arr_2 is array (My_Int range 1 .. 10) of Integer;
   pragma Annotate (GNATProve, Init_By_Proof, Constr_Arr_2);

   type Arr_Rec is array (Positive range <>) of Rec;
   type Holder (D : Natural) is record
      C : Arr_Rec (1 .. D);
   end record;
   type Rec_Rec is record
      C : Rec;
   end record;
   type Rec_Rec_2 is record
      C : Rec_2;
   end record;

   procedure P (X : out Rec) with
     Pre => X.Y'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Rec) with
     Pre => X.Y'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Rec_2) with
     Pre => X.X'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Rec_2) with
     Pre => X.X'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Unc_Arr) with
     Pre => X'Length > 0 and then X (X'First)'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Unc_Arr) with
     Pre => X'Length > 0 and then X (X'First)'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Unc_Arr_2) with
     Pre => X'Length > 0 and then X (X'First)'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Unc_Arr_2) with
     Pre => X'Length > 0 and then X (X'First)'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Constr_Arr) with
     Pre => X (X'First)'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Constr_Arr) with
     Pre => X (X'First)'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Constr_Arr_2) with
     Pre => X (X'First)'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Constr_Arr_2) with
     Pre => X (X'First)'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Arr_Rec) with
     Pre => X'Length > 0 and then X (X'First).Y'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Arr_Rec) with
     Pre => X'Length > 0 and then X (X'First).Y'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Holder) with
     Pre => X.D > 0 and then X.C (1).Y'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Holder) with
     Pre => X.D > 0 and then X.C (1).Y'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Rec_Rec) with
     Pre => X.C.Y'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Rec_Rec) with
     Pre => X.C.Y'Valid_Scalars
   is
   begin
      null;
   end Q;

   procedure P (X : out Rec_Rec_2) with
     Pre => X.C.X'Valid_Scalars
   is
   begin
      null;
   end P;

   procedure Q (X : in out Rec_Rec_2) with
     Pre => X.C.Z'Valid_Scalars
   is
   begin
      null;
   end Q;

   R1 : Rec := (1, 2, True);
   R2 : Rec_2 := (1, 2, True);
   A1 : Unc_Arr (1 .. 10) := (others => 1);
   A2 : Unc_Arr_2 (1 .. 10) := (others => 1);
   A3 : Constr_Arr := (others => 1);
   A4 : Constr_Arr_2 := (others => 1);
   A5 : Arr_Rec (1 .. 10) := (others => (1, 2, True));
   H1 : Holder := (D => 10, C => (others => (1, 2, True)));
   H2 : Holder := (D => 10, C => (others => (1, 2, True)));
   R3 : Rec_Rec := (C => (1, 2, True));
   R4 : Rec_Rec_2 := (C => (1, 2, True));
begin
   if Branch (1) then
      P (R1);--@PRECONDITION:FAIL
   else
      Q (R1);
   end if;
   if Branch (1) then
      P (R2);--@PRECONDITION:FAIL
   else
      Q (R2);
   end if;
   if Branch (1) then
      P (A1);--@PRECONDITION:FAIL
   else
      Q (A1);
   end if;
   if Branch (1) then
      P (A2);--@PRECONDITION:FAIL
   else
      Q (A2);
   end if;
   if Branch (1) then
      P (A3);--@PRECONDITION:FAIL
   else
      Q (A3);
   end if;
   if Branch (1) then
      P (A4);--@PRECONDITION:FAIL
   else
      Q (A4);
   end if;
   if Branch (1) then
      P (A5);--@PRECONDITION:FAIL
   else
      Q (A5);
   end if;
   if Branch (1) then
      P (H1.C);--@PRECONDITION:FAIL
   else
      Q (H1.C);
   end if;
   if Branch (1) then
      P (H2);--@PRECONDITION:FAIL
   else
      Q (H2);
   end if;
   if Branch (1) then
      P (R3);--@PRECONDITION:FAIL
   else
      Q (R3);
   end if;
   if Branch (1) then
      P (R4);--@PRECONDITION:FAIL
   else
      Q (R4);
   end if;
end Test_Init_By_Proof_Out_Params;
