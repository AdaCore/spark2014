procedure Relax_Init with SPARK_Mode is
   type Relaxed is new Natural with Relaxed_Initialization;

   type Rec is record
      A : Natural;
      B : Relaxed;
   end record;

   B : Boolean := True;
begin
   ---------------------------------
   -- A and B are not initialized --
   ---------------------------------

   declare
      R : Rec;
   begin
      pragma Assert (R.A = 0 and R.B = 0);
   end;

   -----------------------------------
   -- A is not and B is initialized --
   -----------------------------------

   declare
      R : Rec;
   begin
      if B then
         R.B := 0;
      end if;

      pragma Assert (R.A = 0 and R.B = 0);
   end;

   ---------------------------------------------
   -- A might not be and B is not initialized --
   ---------------------------------------------

   declare
      R : Rec;
   begin
      if B then
         R.A := 0;
      end if;

      pragma Assert (R.A = 0 and R.B = 0);
   end;

   -----------------------------------------
   -- A might not be and B is initialized --
   -----------------------------------------

   declare
      R : Rec;
   begin
      if B then
         R := (0,0);
      end if;

      pragma Assert (R.A = 0 and R.B = 0);
   end;

   -----------------------------------
   -- A is and B is not initialized --
   -----------------------------------

   declare
      R : Rec;
   begin
      R.A := 0;

      pragma Assert (R.A = 0 and R.B = 0);
   end;

   -----------------------------
   -- A and B are initialized --
   -----------------------------

   declare
      R : Rec;
   begin
      R.A := 0;

      if B then
         R.B := 0;
      end if;

      pragma Assert (R.A = 0 and R.B = 0);
   end;
end Relax_Init;
