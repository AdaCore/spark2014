package body Test is

   ---------------------
   -- Uninitialized_1 --
   ---------------------

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

   ---------------------
   -- Uninitialized_2 --
   ---------------------

   function Uninitialized_2 (A, B : Integer) return Boolean is
   begin
      if A < B then
         return True;
      end if;
      if A > B then
         return False;
      end if;
      raise Program_Error;
   end Uninitialized_2;

   ---------------------
   -- Uninitialized_3 --
   ---------------------

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

   ---------------------
   -- Uninitialized_4 --
   ---------------------

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

   ---------------------
   -- Uninitialized_5 --
   ---------------------

   procedure Uninitialized_5 (A : out Natural; B : Natural := 5) is
      C : Natural;
   begin
      for I in B .. C loop
         A := A * I;
      end loop;
   end Uninitialized_5;

   ------------------------------
   -- Ineffective_Statements_1 --
   ------------------------------

   procedure Ineffective_Statements_1 (A, B : in out Integer) is
   begin
      for I in Integer range A .. B loop
         A := A * I;
         B := 5;
      end loop;
      B := A / 2;
   end Ineffective_Statements_1;

   ------------------------------
   -- Ineffective_Statements_2 --
   ------------------------------

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

   ------------------------------
   -- Ineffective_Statements_3 --
   ------------------------------

   procedure Ineffective_Statements_3 (Export : out Integer) is
      Temp : Integer;

      procedure Initialize_Temp
        with Global  => (Output => Temp),
             Depends => (Temp => null)
      is
      begin
         Temp := 0;
      end Initialize_Temp;

      procedure Edit_Temp (Import : Integer)
         with Global  => (Output => Temp),
              Depends => (Temp => Import)
      is
      begin
         Temp := Import;
      end Edit_Temp;
   begin
      Initialize_Temp;
      Edit_Temp (5);
      Export := Temp;
   end Ineffective_Statements_3;

   ------------------------------
   -- Ineffective_Statements_4 --
   ------------------------------

   procedure Ineffective_Statements_4 (Import : in Natural) is
      Temp : Natural := Import;

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

   ------------------------
   -- Unused_Variables_1 --
   ------------------------

   procedure Unused_Variables_1
   is
      generic
      package G is
         Unused : Integer;
      end G;

      package body G is
      begin
         Unused := 123;
         pragma Assert (Unused /= 456);
      end G;

      package Inst is new G;
   begin
      null;
   end Unused_Variables_1;

   ------------------------
   -- Unused_Variables_2 --
   ------------------------

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

   type Int_Array is array (Integer range 1 .. 100) of Integer;

   ------------------------
   -- Unreachable_Code_1 --
   ------------------------

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
