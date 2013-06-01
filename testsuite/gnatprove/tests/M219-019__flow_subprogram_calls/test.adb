with Other;

package body Test is

   ------------------------------------------------------------
   --  The example from the Horowitz, Reps, Binkley SDG paper
   ------------------------------------------------------------

   procedure HRB_Main (Sum : out Integer)
   is
      procedure HRB_Add (A : in out Integer;
                         B : in out Integer)
      is
      begin
         A := A + B;
      end HRB_Add;

      procedure HRB_Increment (Z : in out Integer)
      is
         Tmp : Integer := 1;
      begin
         HRB_Add (Z, B => Tmp);
      end HRB_Increment;

      procedure HRB_A (X : in out Integer;
                       Y : in out Integer)
      is
      begin
         HRB_Add (X, Y);
         HRB_Increment (Y);
      end HRB_A;

      I   : Integer;
   begin
      Sum := 0;
      I   := 1;
      while I < 11 loop
         HRB_A (Sum, I);
      end loop;
   end HRB_Main;

   ------------------------------------------------------------
   --  This is my silly recursive testcase
   ------------------------------------------------------------

   procedure Flo_Rec_Flush (A, B, C : in out Integer)
   is
   begin
      A := B;
      B := C;
      C := 0;
      if A /= 0 then
         Flo_Rec_Flush (A, B, C);
      end if;
   end Flo_Rec_Flush;

   ------------------------------------------------------------
   --  Tests for IPA v.s. trusting contracts
   ------------------------------------------------------------

   procedure Swap_A (X, Y : in out Integer);
   --  Implemented here, without contracts.

   procedure Swap_B (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Implemented here, with contracts.

   procedure Swap_C (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Using Other.Swap_With_Contract

   procedure Swap_D (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Using Other.Swap_Without_Contract

   procedure Swap_E (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Using Swap_A (no contracts)

   procedure Swap_F (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Using Swap_B (contracts)

   procedure Swap_A (X, Y : in out Integer)
   is
      Tmp : Integer;
   begin
      Tmp := X;
      X := Y;
      Y := Tmp;
   end Swap_A;

   procedure Swap_B (X, Y : in out Integer)
   is
      Tmp : Integer;
   begin
      Tmp := X;
      X := Y;
      Y := Tmp;
   end Swap_B;

   procedure Swap_C (X, Y : in out Integer)
   is
   begin
      Other.Swap_With_Contract (X, Y);
   end Swap_C;

   procedure Swap_D (X, Y : in out Integer)
   is
   begin
      Other.Swap_Without_Contract (X, Y);
   end Swap_D;

   procedure Swap_E (X, Y : in out Integer)
   is
   begin
      Swap_A (X, Y);
   end Swap_E;

   procedure Swap_F (X, Y : in out Integer)
   is
   begin
      Swap_B (X, Y);
   end Swap_F;

   ------------------------------------------------------------
   --  Tests for calling functions
   ------------------------------------------------------------

   function Factorial (N : Positive) return Positive is
   begin
      if N = 1 then
         return 1;
      else
         return N * Factorial (N - 1);
      end if;
   end Factorial;

   procedure Calling_Function_01 (A : Boolean;
                                  N : in out Integer)
   is
   begin
      if A then
         N := 0;
      else
         N := Factorial (N);
      end if;
   end Calling_Function_01;

   ------------------------------------------------------------
   --  Tests for globals
   ------------------------------------------------------------

   procedure Global_Test_01 (N : out Integer)
   is
      Counter : Integer;

      procedure Do_Stuff_A (X : in out Integer)
      with Global  => (In_Out => (Counter)),
           Depends => (X       => X,
                       Counter => Counter);

      procedure Do_Stuff_B (X : Integer)
      with Global => (Output => Counter);

      procedure Do_Stuff_A (X : in out Integer)
      is
      begin
         X       := X + 1;
         Counter := Counter + 1;
      end Do_Stuff_A;

      procedure Do_Stuff_B (X : Integer)
      is
      begin
         if X > 0 then
            Counter := X;
         end if;
      end Do_Stuff_B;

   begin
      N := 10;
      Do_Stuff_A (N);
      Do_Stuff_B (N);
   end Global_Test_01;

   procedure Global_Test_02 (N : out Integer)
   is
      Counter : Integer;

      procedure Do_Stuff_C (X : in out Integer)
      is
      begin
         X       := X + 1;
         Counter := Counter + 1;
      end Do_Stuff_C;

      procedure Do_Stuff_D (X : Integer)
      is
      begin
         Counter := X;
      end Do_Stuff_D;

   begin
      N := 10;
      Do_Stuff_C (N);
      Do_Stuff_D (N);
   end Global_Test_02;

   procedure Global_Test_03 (A : Integer;
                             B : out Integer)
   is
      S : Integer;

      function F return Integer
        with Global => (Input => S);

      function F return Integer
      is
      begin
         return S;
      end F;

   begin

      S := A;
      B := F;

   end Global_Test_03;

   procedure Global_Test_04
   is
      S : Integer;

      procedure Direct_Update_Bad
        with Global => S;

      procedure Direct_Update
        with Global => (Output => S);

      procedure Indirect_Update
        with Global => S;

      procedure Set (X : out Integer);

      procedure Direct_Update_Bad
      is
      begin
         S := 12;
      end Direct_Update_Bad;

      procedure Direct_Update
      is
      begin
         S := 12;
      end Direct_Update;

      procedure Indirect_Update
      is
      begin
         Direct_Update;
         Set (S);
      end Indirect_Update;

      procedure Set (X : out Integer)
      is
      begin
         X := 12;
      end Set;
   begin
      Direct_Update;
   end Global_Test_04;


end Test;
