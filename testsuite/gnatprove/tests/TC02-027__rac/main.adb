with Ada.Text_IO; use Ada.Text_IO;

procedure Main is

   type R1 is range 1 .. 10;

   type R2 is new Integer range 1 .. 10;

   type E1 is (A1, A2, A3);

   type R3 is record
      F1 : Integer;
      F2 : Integer;
   end record;

   type M1 is mod 10;

   type Arr_Ix is range 1 .. 5;

   type Arr1 is array (Arr_Ix) of Integer;
   type Arr2 is array (Arr_Ix) of R3;

   function R3_Image (R : R3) return String is
     ("F1 =>" & Integer'Image (R.F1) & ", F2 =>" & Integer'Image (R.F2));

   procedure Scopes is

      function F1 return Integer is
      begin
         Put_Line ("F");
         return 42;
      end F1;

      procedure F2 (X : in out Integer) is
      begin
         X := X + 1;
      end F2;

      function F3 (X : in out Integer) return Integer is
      begin
         X := X + 1;
         return 1;
      end F3;

      I : Integer := 42;
      J : constant Integer := F1;
      Ignore : Integer;

   --  Start of processing for Scopes

   begin
      Put_Line ("I: " & Integer'Image (I));
      Put_Line ("J: " & Integer'Image (J));
      declare
         I : Integer := 10;
      begin
         Put_Line ("I: " & Integer'Image (I));
         I := I + I;
         Put_Line ("I: " & Integer'Image (I));
      end;
      Put_Line ("I: " & Integer'Image (I));
      I := I + 1;
      Put_Line ("I: " & Integer'Image (I));
      F2 (I);
      Put_Line ("I: " & Integer'Image (I));
      Ignore := F3 (I);
      Put_Line ("I: " & Integer'Image (I));
   end Scopes;

   procedure Operations is
      I : constant Integer := 3;
   begin
      Put_Line (Integer'Image (1 + 2 - 4 ** 5));
      Put_Line (Integer'Image (abs (-I)));
      Put_Line (Boolean'Image (1 > 2) & " - " & Boolean'Image (2 > 1));
      Put_Line (Boolean'Image (True xor True) &
                  " - " & Boolean'Image (True xor False));
      Put_Line (M1'Image (M1'(5) xor M1'(2)));
      Put_Line (M1'Image (M1'(6) and M1'(2)));
      Put_Line (M1'Image (M1'(2) or M1'(1)));
   end Operations;

   procedure Assertions is
      I : Integer;
   begin
      I := 0;
      pragma Assert (I = 0);
      pragma Assert (for all J in R1 => J > 0);
      pragma Assert (not (for all J in R1 => J < 10));
      pragma Assert (for all J in 1 .. 5 => J > 0);
      pragma Assert (not (for all J in 1 .. 5 => J < 5));
      pragma Assert (for all J in R1 range 1 .. 5 => J > 0);
      pragma Assert (not (for all J in R1 range 1 .. 5 => J < 5));
      pragma Assert (5 in R1);
      pragma Assert (not (11 in R1));
   end Assertions;

   procedure Attributes is

      function F1 (X : Integer) return Integer is
        (X) with Post => (F1'Result = 0);

      procedure F2 (X : in out Integer; Y : Integer)
        with Post => (X = X'Old + 1) is
      begin
         X := X + Y;
      end F2;

      procedure F3 (X : in out R3) with
        Post => (X = (X'Old with delta F1 => X'Old.F1 + 1)) is
      begin
         X.F1 := X.F1 + 1;
      end F3;

      I  : Integer;
      X3 : R3 := (F1 => 100, F2 => 10);

   -- Start of processing for Attributes

   begin
      I := F1 (0);
      Put_Line ("I: " & Integer'Image (I));
      F2 (I, 1);
      Put_Line ("I: " & Integer'Image (I));
      Put_Line ("R1'First: " & R1'Image (R1'First));
      Put_Line ("R1'Last: " & R1'Image (R1'Last));
      Put_Line ("R2'First: " & R2'Image (R2'First));
      Put_Line ("R2'Last: " & R2'Image (R2'Last));
      Put_Line ("E1'First: " & E1'Image (E1'First));
      Put_Line ("E1'Last: " & E1'Image (E1'Last));
      Put_Line ("E1'Succ: " & E1'Image (E1'Succ (E1'First)));
      Put_Line ("E1'Pred: " & E1'Image (E1'Pred (E1'Last)));
      Put_Line ("R1'Succ: " & R1'Image (R1'Succ (R1'First)));
      Put_Line ("R1'Pred: " & R1'Image (R1'Pred (R1'Last)));
      Put_Line ("Min: " & Integer'Image (Integer'Min (10, 2)));
      Put_Line ("Max: " & Integer'Image (Integer'Max (10, 2)));
      Put_Line ("R3: " & R3_Image (X3));
      F3 (X3);
      Put_Line ("R3: " & R3_Image (X3));
   end Attributes;

   procedure Aggretates is
      A1 : constant Arr1 := (11, 22, 33, 44, 55);
      A2 : constant Arr1 := (3 => 100, others => 1);
      A3 : constant Arr1 := (1 .. 3 => 0, 4 => 1, others => 2);
      A4 : Arr2 := (1 => (F1 => 1, F2 => 1), others => (F1 => 11, F2 => 11));
      N  : constant Arr_Ix := 2;
   begin
      for J in Arr_Ix loop
         Put_Line (Arr_Ix'Image (J) & " - " & Integer'Image (A1 (J)));
      end loop;
      for J in Arr_Ix loop
         Put_Line (Arr_Ix'Image (J) & " - " & Integer'Image (A2 (J)));
      end loop;
      for J in Arr_Ix loop
         Put_Line (Arr_Ix'Image (J) & " - " & Integer'Image (A3 (J)));
      end loop;
      for J in Arr_Ix loop
         Put_Line (Arr_Ix'Image (J) & " - " & R3_Image (A4 (J)));
      end loop;
      A4 (2) := (F1 => 22, F2 => 22);
      for J in Arr_Ix loop
         Put_Line (Arr_Ix'Image (J) & " - " & R3_Image (A4 (J)));
      end loop;
      pragma Assert ((A1 with delta 1 => 6) =
                     (A1 with delta 1 => 6));
      pragma Assert ((A1 with delta 1 => 6) /=
                     (A1 with delta 2 => 6));
      pragma Assert ((A1 with delta 1 => 5, N => 6) =
                     (A1 with delta N => 6, 1 => 5));
   end Aggretates;

   procedure Assignments is
   begin
      declare
         X1 : R3 := (F1 => 0, F2 => 1);
         X2 : constant R3 := X1;
      begin
         Put_Line ("T1: " & R3_Image (X1) & " - " & R3_Image (X2));
         X1.F1 := 10;
         Put_Line ("T2: " & R3_Image (X1) & " - " & R3_Image (X2));
      end;

      declare
         X2 : Arr1 := (1, 1, 1, 1, 1);
         X3 : Arr1 := (others => 1);
      begin
         Put_Line ("T3: " & Integer'Image (X2 (1)) &
                     " - " & Integer'Image (X2 (2)) &
                     " - " & Integer'Image (X2 (3)));
         X2 (2) := 11;
         Put_Line ("T4: " & Integer'Image (X2 (1)) &
                     " - " & Integer'Image (X2 (2)) &
                     " - " & Integer'Image (X2 (3)));
         X3 (2) := 11;
         Put_Line ("T5: " & Integer'Image (X3 (1)) &
                     " - " & Integer'Image (X3 (2)) &
                     " - " & Integer'Image (X3 (3)));
      end;

      declare
         X1 : R3 := (F1 => 0, F2 => 1);
         X2 : Arr2 := (X1, X1, X1, X1, X1);
         X3 : Arr2 := (others => X1);
      begin
         X1.F1 := 11;
         Put_Line ("T6: " &  R3_Image (X2 (2)) & " - " & R3_Image (X2 (3)));
         X2 (2).F1 := 111;
         Put_Line ("T7: " & R3_Image (X2 (2)) & " - " & R3_Image (X2 (3)));
         Put_Line ("T8: " & R3_Image (X3 (2)) & " - " & R3_Image (X3 (3)));
         X3 (2).F1 := 1111;
         Put_Line ("T9: " & R3_Image (X3 (2)) & " - " & R3_Image (X3 (3)));
      end;
   end Assignments;

   procedure Control is
      I : Integer := 0;
   begin
      for J in 0 .. 2 loop
         Put_Line ("J: " & Integer'Image (J));
         I := I + J;
      end loop;
      Put_Line ("I: " & Integer'Image (I));
      for J in R1 loop
         Put_Line ("J: " & R1'Image (J));
      end loop;
      for J in R2 loop
         Put_Line ("J: " & R2'Image (J));
      end loop;
      for J in R1 range 3 .. 6 loop
         Put_Line ("J: " & R1'Image (J));
      end loop;
      for A in E1 loop
         Put_Line ("A: " & E1'Image (A));
      end loop;
      I := 0;
      while I < 2 loop
         I := I + 1;
         Put_Line ("I: " & Integer'Image (I));
      end loop;
      I := 0;
      loop
         I := I + 1;
         Put_Line ("I: " & Integer'Image (I));
         exit when I = 2;
      end loop;
   end Control;

   procedure Call_Ghost is
      function My_Ghost return String with Ghost is
      begin
         return "hoo!";
      end My_Ghost;
   begin
      pragma Assert (My_Ghost = "hoo!");
   end Call_Ghost;

--  Start of processing for Main

begin
   Put_Line ("Scopes");
   Scopes;
   Put_Line ("Operations");
   Operations;
   Put_Line ("Assertions");
   Assertions;
   Put_Line ("Attributes");
   Attributes;
   Put_Line ("Aggretates");
   Aggretates;
   Put_Line ("Assignments");
   Assignments;
   Put_Line ("Control");
   Control;
   Put_Line ("Ghost");
   Call_Ghost;
end Main;
