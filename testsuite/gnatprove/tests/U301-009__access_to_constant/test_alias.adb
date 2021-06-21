--  Idea: aliases are fine, cannot be deallocated.
--  The designated structure cannot be modified.
--  Allow 'access on (parts of) constant objects if the access type is constant?

procedure Test_Alias with SPARK_Mode is
   type Int_Acc is access Integer;
   type C_Int_Acc is access constant Integer;
   type Rec is record
      F : Int_Acc;
   end record;
   type Rec_Acc is access constant Rec;
   type Holder is record
      C : Rec_Acc;
   end record;
   type Holder_Acc is access Holder;
   type Rec_Acc_2 is access Rec;
   type Holder_2 is record
      C : Rec_Acc_2;
   end record;
   type Holder_2_Acc is access constant Holder_2;

   procedure Do_Something_1 (X : in out Integer) with Import;
   procedure Do_Something_2 (X : Int_Acc) with Import;
   procedure Do_Something_3 (X : in out Int_Acc) with Import;

   procedure Borrow (X : access Integer) with Import;

   function Bad_Borrow_Traverse_1 (X : access Holder) return access Integer is
     (X.C.F);
   -- Bad! Borrow of part of the value designated by a constant pointer
   function Bad_Borrow_Traverse_2 (X : access Holder) return access Integer is
   begin
      return X.C.F;
      -- Bad! Borrow of part of the value designated by a constant pointer
   end Bad_Borrow_Traverse_2;

   function OK_Borrow_Traverse_1 (X : access Holder) return access Holder is
     (X);
   function OK_Borrow_Traverse_2 (X : access Integer) return access Integer is
     (X);

   function Move_Bad (X : Holder_2_Acc) return Int_Acc is
   begin
      return X.C.F;
   end Move_Bad;
   function Move_OK (X : Holder_2_Acc) return C_Int_Acc is
   begin
      return C_Int_Acc (X.C.F);
   end Move_OK;

   Y : Rec_Acc;
   Z : Rec_Acc;
   H : Holder_Acc;
   H_2 : Holder_2_Acc;
   V : Rec;
   U : C_Int_Acc;

   procedure Init with
     Import,
     Global => (Output => (Y, Z, H, H_2, V, U));

begin
   Init;

   Y.F.all := 12;
   --  Bad! Update to an access-to-constant part of an object
   Do_Something_1 (Y.F.all);
   --  Bad! Update to an access-to-constant part of an object
   Do_Something_2 (Y.F);
   --  Bad! Update to an access-to-constant part of an object
   Do_Something_3 (H_2.C.F);
   --  Bad! Move of an access-to-constant part of an object

   declare
      B1 : access Integer := Y.F;
      --  Bad! Borrow of part of the value designated by a constant pointer
      B2 : access Integer := OK_Borrow_Traverse_1 (H).C.F;
      --  Bad! Borrow of part of the value designated by a constant pointer
      B3 : access Integer := OK_Borrow_Traverse_2 (H.C.F);
      --  Bad! Borrow of part of the value designated by a constant pointer
   begin
      B1.all := 15;
   end;

   Borrow (Y.F);
   --  Bad! Borrow of part of the value designated by a constant pointer

   declare
      C1 : access constant Integer := Y.F;
      --  OK, this is an observe
      C2 : access constant Integer := OK_Borrow_Traverse_1 (H).C.F;
      --  OK, this is an observe
      C3 : access constant Integer := OK_Borrow_Traverse_2 (H.C.F);
      --  OK, this is an observe
   begin
      pragma Assert (C1.all = 15);
   end;

   declare
      C : access constant Rec := Y;
      --  OK, this is an observe
   begin
      Z := Rec_Acc (C);
      --  Bad! We cannot put an observer inside another structure
   end;

   declare
      R : constant Rec := Z.all;
      C : Int_Acc := R.F;
      --  OK, aliases are fine
   begin
      pragma Assert (R.F.all = 15);
   end;

   U := C_Int_Acc (Y.F);
   --  OK, aliases are fine

   V := Y.all;
   --  Bad! Move of an access-to-constant part of an object
   V.F.all := 16;

   declare
      S : constant Int_Acc := Y.F;
      --  Bad! Move of an access-to-constant part of an object
   begin
      S.all := 17;
   end;

   declare
      C1 : C_Int_Acc := new Integer'(15); --  Bad! Memory can never be reclaimed
      X2 : Int_Acc := new Integer'(15);
      C2 : C_Int_Acc := C_Int_Acc (X2); --  Bad! Memory can never be reclaimed
      R : constant Rec := Z.all;
      C3 : C_Int_Acc := C_Int_Acc (R.F); --  OK, memory was already frozen

      procedure P (R : Rec; C3 : out C_Int_Acc) is
      begin
         C3  := C_Int_Acc (R.F); --  Bad, the actual for R might be a variable
      end P;

      procedure P (H : Holder; C3 : out C_Int_Acc) is
      begin
         C3  := C_Int_Acc (H.C.F); --  OK, C is a constant part of H
      end P;
   begin
      null;
   end;
end Test_Alias;
