with P;   use P;
procedure Private_Part with SPARK_Mode is
begin
   -----------------------------------------
   -- A record with only a private part B --
   -----------------------------------------

   declare
      R : Private_Only;
   begin

      --------------------------
      -- B is not initialized --
      --------------------------

      pragma Assert (R = R);

      --------------------------------
      -- B might not be initialized --
      --------------------------------

      if E then
         Initialize_Private (R);
      end if;

      pragma Assert (R = R);

      ----------------------
      -- B is initialized --
      ----------------------

      Initialize_Private (R);

      pragma Assert (R = R);

   end;

   --------------------------------------------------------
   -- A record with a normal part A and a private part B --
   --------------------------------------------------------

      ----------------------------------
      -- A and B are not initialiazed --
      ----------------------------------

   declare
      R : Normal_And_Private;
   begin
      pragma Assert (R = R);
   end;

      ---------------------------------------------------------
      -- A is not initialized and B might not be initialized --
      ---------------------------------------------------------

   declare
      R: Normal_Rec_And_Private;
   begin
      if E then
         Initialize_Normal_Rec_And_Private (R);
      end if;

      begin
         Raise_Exception (R.A);
      exception
         when My_Exception =>
            pragma Assert (R = R);
      end;
   end;

      -----------------------------------------------
      -- A is not initialized and B is initialized --
      -----------------------------------------------

   declare
      R: Normal_Rec_And_Private;
   begin
      Initialize_Normal_Rec_And_Private (R);

      begin
         Raise_Exception (R.A);
      exception
         when My_Exception =>
            pragma Assert (R = R);
      end;
   end;

   declare
      R : Normal_And_Private;
   begin

      if E then
         R.A := 0;
      end if;

      ---------------------------------------------------------
      -- A might not be initialized and B is not initialized --
      ---------------------------------------------------------

      pragma Assert (R = R);

      --------------------------------------
      -- A and B might not be initialized --
      --------------------------------------

      if E then
         Initialize_Normal_Private (R);
      end if;

      pragma Assert (R = R);
   end;
      -----------------------------------------------------
      -- A might not be initialized and B is initialized --
      -----------------------------------------------------

   declare
      R: Normal_Rec_And_Private;
   begin

      Initialize_Normal_Rec_And_Private (R);

      begin
         Raise_Exception (R.A);
      exception
         when My_Exception =>
            if E then
               R.A.A := 0;
            end if;

            pragma Assert (R = R);
      end;
   end;

   declare
      R : Normal_And_Private;
   begin
      -----------------------------------------------
      -- A is initialized and B is not initialized --
      -----------------------------------------------

      R.A := 0;
      pragma Assert (R = R);
   end;

   declare
      R : Normal_And_Private;
   begin
      -----------------------------------------------------
      -- A is initialized and B might not be initialized --
      -----------------------------------------------------

      if E then
         Initialize_Normal_Private (R);
      end if;

      R.A := 0;
      pragma Assert (R = R);

      -----------------------------
      -- A and B are initialized --
      -----------------------------

      Initialize_Normal_Private (R);

      pragma Assert (R = R);
   end;
end Private_Part;
