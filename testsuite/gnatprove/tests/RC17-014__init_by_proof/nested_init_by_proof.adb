procedure Nested_Init_By_Proof with SPARK_Mode is
   type My_Nat is new Natural;

   type Rec (D : Boolean := False) is record
      F2 : My_Nat;
      case D is
      when True =>
      F1 : My_Nat := 15;
      when False =>
      F3 : My_Nat;
      end case;
   end record;
   pragma Annotate (GNATprove, Init_By_Proof, Rec);

   function My_Eq (X, Y : Rec) return Boolean is
     (X.D = Y.D
      and then X.F2'Valid_Scalars = Y.F2'Valid_Scalars
      and then (if X.F2'Valid_Scalars then X.F2 = Y.F2)
      and then
      (if X.D then X.F1'Valid_Scalars = Y.F1'Valid_Scalars
         and then (if X.F1'Valid_Scalars then X.F1 = Y.F1)
       else X.F3'Valid_Scalars = Y.F3'Valid_Scalars
         and then (if X.F3'Valid_Scalars then X.F3 = Y.F3)));

   type My_Arr is array (My_Nat range <>) of Rec;

   type Holder (D : My_Nat) is record
      Content : My_Arr (1 .. D);
   end record;

   procedure Init (X : out My_Nat) is
   begin
      X := 14;
   end Init;

   procedure Assign (X : in out My_Nat) is
   begin
      X := 15;
   end Assign;

   procedure Init_F3 (X : in out Rec) with
     Post => X.D = X.D'Old
     and then (if X.D then My_Eq (X, X'Old)
               else X.F3'Valid_Scalars
               and then X.F2'Valid_Scalars = X'Old.F2'Valid_Scalars
               and then (if X.F2'Valid_Scalars then
                             X.F2 = X'Old.F2))
   is
   begin
      if not X.D then
         X.F3 := 14;
      end if;
   end Init_F3;

   X : Holder (15);
   C : My_Nat;
   B : Boolean;
   R : Rec (True);
begin
   X.Content (10) := (D => True, F1 => 0, F2 => 0);
   pragma Assert (X.Content(10)'Valid_Scalars);
   X.Content (8) := R;
   X.Content (8).F2 := 14;
   pragma Assert (X.Content(8)'Valid_Scalars);
   Init (X.Content (6).F2);
   Assign (X.Content (6).F2);
   Init_F3 (X.Content (6));
   pragma Assert (X.Content(6)'Valid_Scalars);
   C := X.Content (10).F1;
   C := X.Content (12).F3; -- @INIT_BY_PROOF:FAIL
end Nested_Init_By_Proof;
