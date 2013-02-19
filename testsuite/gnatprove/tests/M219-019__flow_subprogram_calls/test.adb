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
   begin
      HRB_Add (Z, 1);
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
   --  This is my silly testcase
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

end Test;
