procedure Test with SPARK_Mode is

   procedure Test_Unconstrained_Record is
      type Rec (X : Boolean) is record
         case X is
         when True => I : Integer;
         when False => null;
         end case;
      end record;

      procedure P (X : Rec) with Pre => True;

      procedure P (X : Rec) is
      begin
         pragma Assert (X'Size = 64); --  @ASSERT:FAIL
      end P;

      X : Rec (True) := (True, 12);
      Y : Rec (False) := (X => False);
   begin
      P (X);
      P (Y);
   end;

   procedure Test_Slice is
      type Bool_Array is array (Integer range <>) of Boolean;
      A : Bool_Array := (1 .. 10 => True);

      procedure P (A : Bool_Array; L : Natural) with
        Pre => A'First = 1 and A'Last >= 5 and L = 5;
      procedure P (A : Bool_Array; L : Natural) is
      begin
         pragma Assert (A (1 .. L)'Size = 40); --  @ASSERT:PASS
      end P;

   begin
      P (A, 5);
   end;

   procedure Test_Slice_2 is
      function Id (X : Integer) return Integer is (X);
      C : constant Integer := Id (5);
      type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;
      type A_Array is array (Integer range <>) of Bool_Array;
      A : A_Array := (1 .. 10 => (others => True));

      procedure P (A : A_Array; L : Natural) with
        Pre => A'First = 1 and A'Last >= 5 and L = 5;
      procedure P (A : A_Array; L : Natural) is
      begin
         pragma Assert (A (1 .. L)'Size = A_Array'Object_Size); --  @ASSERT:FAIL
      end P;

   begin
      P (A, 5);
   end;

   procedure Test_Deref is
      type R is record
         F, G : Integer;
      end record with Object_Size => 128;
      type R_Access is not null access all R;
      X : aliased R := (others => 1);

      procedure P (X : R_Access) with
        Pre => True;
      procedure P (X : R_Access) is
      begin
         pragma Assert (X.all'Size = 128); --  @ASSERT:PASS
      end P;

      C :  R_Access := X'Access;
   begin
      P (C);
   end;

   procedure Test_Deref_Array is
      type Bool_Array is array (Integer range <>) of Boolean;
      type A_Access is not null access all Bool_Array;
      X : aliased Bool_Array := (1 .. 5 => True);

      procedure P (X : A_Access) with
        Pre => True;
      procedure P (X : A_Access) is
      begin
         pragma Assert (X.all'Size = Bool_Array'Object_Size); --  @ASSERT:FAIL
      end P;

      C :  A_Access := X'Access;
   begin
      P (C);
   end;

   procedure Test_Deref_Array_2 is
      type Bool_Array is array (Integer range <>) of Boolean with Pack;
      type A_Access is not null access all Bool_Array;
      X : aliased Bool_Array := (1 .. 5 => True);

      procedure P (X : A_Access) with
        Pre => True;
      procedure P (X : A_Access) is
      begin
         pragma Assert (X.all'Size = Bool_Array'Object_Size); --  @ASSERT:FAIL
      end P;

      C :  A_Access := X'Access;
   begin
      P (C);
   end;

   procedure Test_Array_Comp is
      type V is record
         F, G : Integer;
      end record with Object_Size => 128;
      type A_Array is array (Integer range <>) of V with Pack;
      X : A_Array := (1 .. 5 => (others => 1));

      procedure P (X : A_Array) with
        Pre => 2 in X'Range;
      procedure P (X : A_Array) is
      begin
         pragma Assert (X (2)'Size = V'Object_Size); -- @ASSERT:FAIL
      end P;

   begin
      P (X);
   end;

   procedure Test_Record_Comp is
      type V is record
         F, G : Integer;
      end record with Object_Size => 128;
      type R is record
         F, G : V;
      end record with Pack;
      X : R := (others => (others => 1));

      procedure P (X : R) with
        Pre => True;
      procedure P (X : R) is
      begin
         pragma Assert (X.F'Size = V'Object_Size); -- @ASSERT:FAIL
      end P;

   begin
      P (X);
   end;

   procedure Test_Array_Comp_2 is
      function Id (X : Integer) return Integer is (X);
      C : constant Integer := Id (5);
      type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;
      type A_Array is array (Integer range <>) of Bool_Array with Pack;
      X : A_Array := (1 .. 5 => (others => True));

      procedure P (X : A_Array) with
        Pre => 2 in X'Range;
      procedure P (X : A_Array) is
      begin
         pragma Assert (X (2)'Size = Bool_Array'Object_Size); --  This seems to actually be Valid with GNAT, but it should not be provable
      end P;

   begin
      P (X);
   end;

   procedure Test_Record_Comp_2 is
      function Id (X : Integer) return Integer is (X);
      C : constant Integer := Id (5);
      type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;
      type R is record
         F, G : Bool_Array;
      end record with Pack;
      X : R := (others => (others => True));

      procedure P (X : R) with
        Pre => True;
      procedure P (X : R) is
      begin
         pragma Assert (X.F'Size = Bool_Array'Object_Size); --  This seems to actually be Valid with GNAT, but it should not be provable
      end P;

   begin
      P (X);
   end;

begin
   Test_Array_Comp;
end;
