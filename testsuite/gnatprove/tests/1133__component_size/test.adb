procedure Test with SPARK_Mode is

   procedure Test_Array_Comp is
      type V is record
         F, G : Integer;
      end record with Object_Size => 128;
      type A_Array is array (Integer range <>) of V;
      X : A_Array := (1 .. 5 => (others => 1));

      procedure P (X : A_Array) with
        Pre => 2 in X'Range;
      procedure P (X : A_Array) is
      begin
         pragma Assert (X'Component_Size = V'Object_Size); -- @ASSERT:PASS
      end P;

   begin
      P (X);
   end;

   procedure Test_Array_Comp_2 is
      type V is record
         F, G : Integer;
      end record with Object_Size => 128;
      type A_Array is array (Integer range <>) of V with Pack;
      X : A_Array := (1 .. 5 => (others => 1));

      procedure P (X : A_Array) with
        Pre => 2 in X'Range;
      procedure P (X : A_Array) is
      begin
         pragma Assert (X'Component_Size = V'Size); -- @ASSERT:PASS
      end P;

   begin
      P (X);
   end;

   procedure Test_Array_Comp_3 is
      function Id (X : Integer) return Integer is (X);
      C : constant Integer := Id (5);
      type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;
      type A_Array is array (Integer range <>) of Bool_Array with Pack;
      X : A_Array := (1 .. 5 => (others => True));

      procedure P (X : A_Array) with
        Pre => 2 in X'Range;
      procedure P (X : A_Array) is
      begin
         pragma Assert (X'Component_Size = Bool_Array'Size); --  'Component_Size is imprecisely handled
      end P;

   begin
      P (X);
   end;

   procedure Test_Array_Comp_4 is
      function Id (X : Integer) return Integer is (X);
      C : constant Integer := Id (5);
      type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;
      type A_Array is array (Integer range <>) of Bool_Array;
      X : A_Array := (1 .. 5 => (others => True));

      procedure P (X : A_Array) with
        Pre => 2 in X'Range;
      procedure P (X : A_Array) is
      begin
         pragma Assert (X'Component_Size = Bool_Array'Object_Size); --  'Component_Size is imprecisely handled
      end P;

   begin
      P (X);
   end;

begin
   null;
end;
