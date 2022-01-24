with Ada.Containers; use Ada.Containers;

procedure Main with SPARK_Mode is
   subtype String_1_5 is String (1 .. 5);
   procedure P1 (S : String_1_5) with
     Global => null
   is
   begin
      pragma Assert (S (1) /= 'h'); --@ASSERT:FAIL
   end P1;

   procedure P2 (S : String) with
     Global => null,
     Pre => S'First = 1 and S'Last = 5
   is
   begin
      pragma Assert (S'Last = 1 or else S (2) /= 'h'); --@ASSERT:FAIL
   end P2;

   type Int_Acc is access Integer;
   type Holder is record
      C : Int_Acc;
   end record;
   procedure P3 (H : Holder) with
     Global => null,
     Pre => H.C /= null and then H.C.all = 3
   is
   begin
      pragma Assert (H.C.all = 5); --@ASSERT:FAIL
   end P3;

   type My_Int is new Integer with Relaxed_Initialization;
   type My_Int_Arr is array (1 .. 2) of My_Int;
   procedure P4 (A : My_Int_Arr) with
     Global => null,
     Pre => A (1)'Initialized
   is
   begin
      pragma Assert (A'Initialized); --@ASSERT:FAIL
   end P4;

   type Int_Arr is array (1 .. 6) of Integer;
   procedure P5 (A : Int_Arr) with
     Global => null,
     Pre => A (1) = 1 and A (2) = 1
   is
   begin
      pragma Assert (for all E of A => E /= 1); --@ASSERT:FAIL
   end P5;

   type String_Acc is access String;
   type Holder_S (L : Natural) is record
      S : String_Acc (1 .. L);
   end record;

   procedure P6 (H : Holder_S) with
     Global => null,
     Pre => H.L = 1 and then H.S /= null and then H.S (1) = 'h'
   is
   begin
      pragma Assert (H.S (1) /= 'h'); --@ASSERT:FAIL
   end P6;

   package Nested is
      type Root is tagged record
         F : Integer := 1;
      end record;

      package Nested is
         type Child is new Root with private;
      private
         type Child is new Root with record
            G : Integer := 1;
         end record;
      end Nested;

      type Grand_Child is new Nested.Child with record
         G : Integer := 2;
      end record;
   end Nested;

   procedure P7 with
     Global => null
   is
      X : Nested.Grand_Child;
   begin
      pragma Assert (X.G = 1); --@ASSERT:FAIL
   end P7;

   type Kind is (F1, F2, I1, I2, B);

   type D_Rec (K : Kind) is record
      X : Integer;
      W : Float;
      case K is
         when I1 .. I2 =>
            Y : Integer;
            case K is
            when I1 =>
               Z : Integer;
            when others =>
               null;
            end case;
         when F1 | F2 =>
            Fl : Float;
         when others =>
            B : Boolean;
      end case;
   end record;

   procedure P8 (X : D_Rec) with
     Global => null,
     Pre => X.X = 1 and then X.W = 3.0 and then
     (case X.K is
        when I1 => X.Y = 1 and X.Z = 1,
        when I2 => X.Y = 1,
        when B  => X.B,
        when others => X.Fl = 3.0)
   is
   begin
      case X.K is
        when I1 =>
            pragma Assert (X.Z /= 1); --@ASSERT:FAIL
        when I2 =>
            pragma Assert (X.Y /= 1); --@ASSERT:FAIL
        when B  =>
            pragma Assert (not X.B); --@ASSERT:FAIL
        when F1 | F2 =>
            pragma Assert (X.Fl /= 3.0); --@ASSERT:FAIL
      end case;
   end P8;

begin
   null;
end Main;
