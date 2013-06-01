package body Test is

   function Uninitialized_1 (Condition : Boolean := False) return Integer is
      X, Y : Integer;
   begin
      if Condition then
         X := 1;
         Y := 2;
      else
         X := 3;
      end if;
      return Y - X;
   end Uninitialized_1;

   function Uninitialized_2 (A, B : Integer) return Boolean is
   begin
      if A < B then
         return True;
      end if;
      if A > B then
         return False;
      end if;
   end Uninitialized_2;

   procedure Uninitialized_3 (A, B : in Integer ; C : out Integer) is
   begin
      for L in A .. B loop
         if L > (A + B) / 2 then
            C := L;
            exit;
         end if;
         exit when L < (A + B) / 2;
      end loop;
      if B < A then
         C := 5;
      end if;
   end Uninitialized_3;

   procedure Uninitialized_4 (Export : out Integer) is
      A : Integer := 0;
      B : Integer := 100;
   begin
      outer: 
         loop
            A := A + 1;
            inner:
               while B > A loop
                  exit outer when B >= A;
                  B := B - 1; 
                  Export := B;
               end loop inner;
         end loop outer;
   end Uninitialized_4;

   procedure Uninitialized_5 (A : out Natural; B : Natural := 5) is
      C : Natural;
   begin
      for I in B .. C loop
         A := A * I;
      end loop;
   end Uninitialized_5;

   procedure Ineffective_Statements_1 (A, B : in out Integer) is
   begin
      for I in Integer range A .. B loop
         A := A * I;
         B := 5;
      end loop;
      B := A / 2;
   end Ineffective_Statements_1;

   procedure Ineffective_Statements_2 (A, B : in out Integer) is
   begin
      if A < B then
         A := 5;
      else
         A := 6;
      end if;
      B := 5;
      A := B;
   end Ineffective_Statements_2;

   procedure Ineffective_Statements_3 (Export : out Integer) is
      Temp : Integer;

      procedure Initialize_Temp
         with Global  => (Output => Temp),
              Depends => (Temp => null);

      procedure Edit_Temp (Import : Integer)
         with Global  => (Output => Temp),
              Depends => (Temp => Import);

      procedure Initialize_Temp
      is
      begin
         Temp := 0;
      end Initialize_Temp;

      procedure Edit_Temp (Import : Integer)
      is
      begin
         Temp := Import;
      end Edit_Temp;
   begin
      Initialize_Temp;
      Edit_Temp (5);
      Export := Temp;
   end Ineffective_Statements_3;

   procedure Ineffective_Statements_4 (Import : in Natural) is
      Temp : Natural := Import;

      function Factorial (Val : Natural) return Natural;

      function Factorial (Val : Natural) return Natural is
      begin
         if Val > 1 then
            return Val * Factorial (Val - 1);
         end if;

         return 1;
      end Factorial;
   begin
      Temp := Factorial (5);
   end Ineffective_Statements_4;

--  We do not process generic packages yet.

--   procedure Unused_Variables_1 is
--      Unused : integer;

--      generic
--      package G is
--      end G;
 
--      package body G is
--      begin
--        Unused := 123;
--        pragma Assert (Unused /= 456);
--      end G;

--      package Inst is new G;

--   begin
--      null;
--   end Unused_Variables_1;

   function Unused_Variables_2 (Par1, Par2 : Integer) return Integer
   is
      X, Y, Z: Integer;

      function Return_X return Integer
         with Global => (X, Y);

      function Return_X return Integer is
      begin
         return X;
      end Return_X;
   begin
      X := -11;
      Y := 2;
      return Return_X + Par1 - Y;
   end Unused_Variables_2;


--  We do not process arrays yet.

--   type Int_Array is array (Integer range 1 .. 100) of Integer;

--   procedure Loop_Stability_1 (Arr : in out Int_Array) is
--   begin
--      for I in Arr (1) .. Arr (2) loop
--         Arr (5) := Arr (6);
--      end loop;
--   end Loop_Stability_1;

   function Loop_Stability_2 return Integer is
      A : Integer;
   begin
      for I in 1 .. 100 loop
         if True then
            A := I * 3;
         else
            A := 5;
         end if;
      end loop;

      return A;
   end Loop_Stability_2;

   function Loop_Stability_3 return Integer is
      I : Integer := 1;
   begin
      while I <= 100 loop
         for J in 1 .. I loop
            I := 1;
         end loop;
      end loop;

      return I;
   end Loop_Stability_3;

   procedure Loop_Stability_4 (Export : out Integer) is
      A, B, C : Integer;
   begin
      A := 20;
      while A < 100 loop
         B := A / 2;
         C := 10;
         A := C + 10;
      end loop;
      Export := A + B + C;
   end Loop_Stability_4;

   --  Loop_Stability_5 does not work correctly yet.
   --  It does not identify the second loop as stable.

   function Loop_Stability_5 return Integer is
      A: Integer;

      procedure Edit_A
         with Global  => (Output => A),
              Depends => (A => null);

      procedure Edit_A
      is
      begin
         A := 10;
      end Edit_A;

      function Return_5 return Integer is
      begin
         return 5;
      end Return_5;
   begin
      while A < 100 loop
         Edit_A;
      end loop;
      loop
         A := Return_5;
         exit when A > 1000;
      end loop;
      return A;
   end Loop_Stability_5;

   procedure Unreachable_Code_1 (Condition : Boolean) is
      X : Boolean;
   begin
      if Condition then
         return;
         X := True;
      else
         loop
            exit;
            X := False;
         end loop;
      end if;
   end Unreachable_Code_1;
end Test;
