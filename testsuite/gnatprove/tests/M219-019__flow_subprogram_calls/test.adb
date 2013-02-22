with Other;

package body Test is

   ------------------------------------------------------------
   --  The example from the Horowitz, Reps, Binkley SDG paper
   ------------------------------------------------------------

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

   procedure HRB_Main (Sum : out Integer)
   is
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

end Test;
