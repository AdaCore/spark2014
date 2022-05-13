procedure Main with SPARK_Mode is
   type Use_User_Eq is record
      F, G : Integer;
   end record;
   function "=" (X, Y : Use_User_Eq) return Boolean with Import;

   package Private_Types is

      type My_Int is private;
      type My_Float is private;
      type Rec_1 is private;
      type Rec_2 is private;
      type Rec_3 is private;
      type Rec_4 (<>) is private;
      type Rec_5 is private;
      type D_Rec_1 (L : Natural) is private;
      type D_Rec_2 (L : Natural) is private;
      type D_Rec_3 is private;
      type D_Rec_4 (L : Natural) is private;
      type D_Rec_5 (L : Natural) is private;
      type Arr_1 is private;
      type Arr_2 is private;
      type Arr_3 is private;
      type Arr_4 (<>) is private;
      type Acc_1 is private;
      type Acc_2 is private;
      type Acc_3 is private;
   private
      pragma SPARK_Mode (Off);
      type My_Int is new Integer;
      type My_Float is new Float;
      type Rec_1 is record
         F1 : Integer;
         F2 : My_Int;
      end record;
      type Rec_2 is record
         F1 : Integer;
         F2 : Float;
      end record;
      type Rec_3 is record
         F1 : Integer;
         F2 : Use_User_Eq;
      end record;
      type Rec_5 is tagged record
         F1 : Integer;
      end record;
      type D_Rec_1 (L : Natural) is record
         F1 : Integer;
         F2 : My_Int;
      end record;
      type D_Rec_2 (L : Natural) is record
         case L is
            when 0 =>
               F1 : Integer;
            when others =>
               F2 : Float;
         end case;
      end record;
      type D_Rec_3 is new D_Rec_2 (0);
      type D_Rec_4 (L : Natural) is tagged record
         F1 : Integer;
      end record;
      type D_Rec_5 (L : Natural) is new D_Rec_4 (L) with record
         F2 : Integer;
      end record;
      type Arr_1 is array (Positive range 1 .. 100) of Natural;
      type Arr_2 is array (Positive range 1 .. 100) of Float;
      type Arr_3 is array (Positive range 1 .. 100) of Use_User_Eq;
      type Arr_4 is array (Positive range <>) of Natural;
      type Rec_4 (L : Natural) is record
         F1 : Integer;
         F2 : Arr_4 (1 .. L);
      end record;
      type Acc_1 is access all Integer;
      type Acc_2 is access all Float;
      type Acc_3 is access all Arr_4;
   end Private_Types;
   use Private_Types;

   procedure Test (X, Y : My_Int) with
     Global => null,
     Pre => X = Y
   is
      function F (X : My_Int) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : My_Float) with
     Global => null,
     Pre => X = Y
   is
      function F (X : My_Float) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence with Eq on floating point
   end Test;

   procedure Test (X, Y : Rec_1) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Rec_1) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : Rec_2) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Rec_2) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence with Eq on floating point
   end Test;

   procedure Test (X, Y : Rec_3) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Rec_3) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence, uses user eq
   end Test;

   procedure Test (X, Y : Rec_4) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Rec_4) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : Rec_5) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Rec_5) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence, tagged type might contain extension part
   end Test;

   procedure Test (X, Y : D_Rec_1) with
     Global => null,
     Pre => X = Y
   is
      function F (X : D_Rec_1) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : D_Rec_2) with
     Global => null,
     Pre => X = Y
   is
      function F (X : D_Rec_2) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence with Eq on floating point
   end Test;

   procedure Test (X, Y : D_Rec_3) with
     Global => null,
     Pre => X = Y
   is
      function F (X : D_Rec_3) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
                                     --  floating point component cannot occur in constrained type
   end Test;

   procedure Test (X, Y : D_Rec_4) with
     Global => null,
     Pre => X = Y
   is
      function F (X : D_Rec_4) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence, tagged type might contain extension part
   end Test;

   procedure Test (X, Y : D_Rec_5) with
     Global => null,
     Pre => X = Y
   is
      function F (X : D_Rec_5) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence, tagged type might contain extension part
   end Test;

   procedure Test (X, Y : Arr_1) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Arr_1) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : Arr_2) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Arr_2) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence with Eq on floating point
   end Test;

   procedure Test (X, Y : Arr_3) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Arr_3) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence, uses user eq
   end Test;

   procedure Test (X, Y : Arr_4) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Arr_4) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:FAIL
                                     --  no congruence, bounds are not checked by = on uncontsrained arrays
   end Test;

   procedure Test (X, Y : Acc_1) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Acc_1) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : Acc_2) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Acc_2) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;

   procedure Test (X, Y : Acc_3) with
     Global => null,
     Pre => X = Y
   is
      function F (X : Acc_3) return Boolean with Import;
   begin
      pragma Assert (F (X) = F (Y)); --@ASSERT:PASS
   end Test;
begin
   null;
end Main;
