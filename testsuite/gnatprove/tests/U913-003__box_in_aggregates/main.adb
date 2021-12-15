procedure Main with SPARK_Mode is
   procedure Test1 with Pre => True, Global => null is
      package Nested is
         type T is private with Default_Initial_Condition => True;
      private
         type T is new Integer; --  Here flow analysis should complain, T is not initialized
      end Nested;
      use all type Nested.T;

      type Holder is record
         F : Nested.T;
      end record;
   begin
      pragma Assert (Holder'(F => <>) = Holder'(F => <>));
   end Test1;

   procedure Test2 with Pre => True, Global => null is
      type Base is new Integer with Default_Value => -5; --@RANGE_CHECK:FAIL
      function Id (X : Base) return Base is (X);
      subtype T is Base range Id (1) .. 5;

      type Holder is record
         F : T;
      end record;
      function P (Dummy : Holder) return Boolean is (True);
   begin
      pragma Assert (P (Holder'(F => <>)));
   end Test2;

   procedure Test3 with Pre => True, Global => null is
      type T is new Integer with Default_Value => -5;

      type Holder is record
         F : T;
      end record;
   begin
      pragma Assert (Holder'(F => <>) = Holder'(F => <>));
   end Test3;

   procedure Test4 with Pre => True, Global => null is
      type Base is new Integer with Default_Value => -5;
      function Id (X : Base) return Base is (X);
      subtype T is Base range Id (1) .. 5;

      type R (P : Boolean := False) is record
         case P is
         when True => F : T;
         when False => null;
         end case;
      end record;

      type Holder is record
         F : R;
      end record;
   begin
      pragma Assert (Holder'(F => <>) = Holder'(F => <>));
      pragma Assert (False); --@ASSERT:FAIL
   end Test4;

   procedure Test5 with Pre => True, Global => null is
      package Nested is
         type T is private with Default_Initial_Condition;
      private
         type Cont is new Integer with Relaxed_Initialization;
         type T is record --  Here flow analysis complains, I don't think it should
            X : Integer := 0;
            Y : Cont;
         end record;
      end Nested;
      use all type Nested.T;

      type Holder is record
         F : Nested.T;
      end record;
   begin
      pragma Assert (Holder'(F => <>) = Holder'(F => <>)); --@INIT_BY_PROOF:FAIL
   end Test5;

   procedure Test6 (I : Integer) with Pre => True, Global => null is
      package Nested is
         type T is private with
           Default_Initial_Condition => P (T);
         function P (X : T) return Boolean;
      private
         pragma SPARK_Mode (Off);
         type T is new Integer;
         function P (X : T) return Boolean is (True);
      end Nested;
      use all type Nested.T;

      type Holder is record
         F : Nested.T;
      end record;
   begin
      if I = 0 then
         pragma Assert (Nested.P (Holder'(F => <>).F)); --  currently unproved, we ignore the DIC to ensure soundness
      else
         declare
            X : Holder := Holder'(F => <>);
         begin
            pragma Assert (Nested.P (X.F)); --@ASSERT:PASS
         end;
      end if;
   end Test6;

   procedure Test7 (I : Integer) with Pre => True, Global => null is
      package Nested is
         type T (D : Boolean := True) is private with
           Default_Initial_Condition => P (T);
         function P (X : T) return Boolean;
      private
         pragma SPARK_Mode (Off);
         type T (D : Boolean := True) is null record;
         function P (X : T) return Boolean is (True);
      end Nested;
      use all type Nested.T;

      type Holder is record
         F : Nested.T;
      end record;
   begin
      if I = 0 then
         pragma Assert (Nested.P (Holder'(F => <>).F)); --  currently unproved, we ignore the DIC to ensure soundness
      else
         declare
            X : Holder := Holder'(F => <>);
         begin
            pragma Assert (Nested.P (X.F)); --@ASSERT:PASS
         end;
      end if;
   end Test7;

   procedure Test8 (I : Integer) with Pre => True, Global => null is
      package Nested is
         type T is private with
           Default_Initial_Condition => P (T);
         function P (X : T) return Boolean;
      private
         pragma SPARK_Mode (Off);
         type T is new Integer;
         function P (X : T) return Boolean is (True);
      end Nested;
      use all type Nested.T;

      type My_Integer is new Integer with Default_Value => 6;

      type Holder is record
         F : Nested.T;
         I : My_Integer;
      end record with Relaxed_Initialization;
   begin
      if I = 0 then
         pragma Assert (Nested.P (Holder'(others => <>).F)); --  currently unproved, we ignore the DIC to ensure soundness
         pragma Assert (Holder'(others => <>).I = 6);
      else
         declare
            X : Holder := Holder'(others => <>);
         begin
            pragma Assert (Nested.P (X.F)); --@ASSERT:PASS
         end;
      end if;
   end Test8;

   procedure Test9 (I : Integer) with Pre => True, Global => null is
      package Nested is
         type T (D : Boolean := True) is private with
           Default_Initial_Condition => P (T);
         function P (X : T) return Boolean;
      private
         pragma SPARK_Mode (Off);
         type T (D : Boolean := True) is null record;
         function P (X : T) return Boolean is (True);
      end Nested;
      use all type Nested.T;

      type Holder is record
         F : Nested.T;
         I : Integer := 14;
      end record with Relaxed_Initialization;
   begin
      if I = 0 then
         pragma Assert (Nested.P (Holder'(others => <>).F)); --  currently unproved, we ignore the DIC to ensure soundness
         pragma Assert (Holder'(others => <>).I = 14);
      else
         declare
            X : Holder := Holder'(others => <>);
         begin
            pragma Assert (Nested.P (X.F)); --@ASSERT:PASS
         end;
      end if;
   end Test9;

   procedure Test10 with Pre => True, Global => null is
      type T is new Integer with Default_Value => 0;

      type Holder is array (Positive range 1 .. 2) of T;
   begin
      pragma Assert (Holder'(others => <>) (1) = 0);
   end Test10;

   procedure Test11 with Pre => True, Global => null is
      type Base is new Integer with Default_Value => -5; --@RANGE_CHECK:FAIL
      function Id (X : Base) return Base is (X);
      subtype T is Base range Id (1) .. 5;

      type Holder is array (Positive range 1 .. 2) of T;
      function P (Dummy : Holder) return Boolean is (True);
   begin
      pragma Assert (P (Holder'(others => <>)));
   end Test11;

   procedure Test12 with Pre => True, Global => null is
      type T is new Integer with Default_Value => 0;

      type Holder is array (Positive range 1 .. 2, Positive range 1 .. 2) of T;
   begin
      pragma Assert (Holder'(others => (others => <>)) (1, 1) = 0);
      pragma Assert (Holder'(for I in others => (others => <>)) (1, 1) = 0);
   end Test12;

   procedure Test13 with Pre => True, Global => null is
      type Base is new Integer with Default_Value => -5; --@RANGE_CHECK:FAIL
      function Id (X : Base) return Base is (X);
      subtype T is Base range Id (1) .. 5;

      type Holder is array (Positive range 1 .. 2, Positive range 1 .. 2) of T;
      function P (Dummy : Holder) return Boolean is (True);
   begin
      pragma Assert (P (Holder'(for I in others => (others => <>))));
   end Test13;

begin
   null;
end;
