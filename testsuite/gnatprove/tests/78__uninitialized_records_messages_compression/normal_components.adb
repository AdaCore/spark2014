with P;   use P;
procedure Normal_Components with SPARK_Mode is
begin
   ---------------------------------------------------------------
   -- Natural_And_Rec: {C: Natural, D.A: Natural, D.B: Natural} --
   ---------------------------------------------------------------

   declare
      S, T : Natural_And_Rec;
   begin
      ------------------------------------
      -- C, A and B are not initialized --
      ------------------------------------

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      -------------------------------------------------------
      -- C is not, A might not be and B is not initialized --
      -------------------------------------------------------

      if E then
         S.D.A := 0;
      end if;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ---------------------------------------------------
      -- C is not and A and B might not be initialized --
      ---------------------------------------------------

      if E then
         S.D.B := 0;
      end if;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ----------------------------------------------------
      -- C is not, A is, and B might not be initialized --
      ----------------------------------------------------

      S.D.A := 0;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ----------------------------------------------
      -- C is not, A is, and B is not initialized --
      ----------------------------------------------

      T.D.A := 0;

      pragma Assert (T.D.A = T.D.B and T.D.A = T.C);

      pragma Assert (T.D.A = T.D.B);

      pragma Assert (T.D.A = T.C);

      pragma Assert (T.D.A = 0);
      pragma Assert (T.D.B = 0);
      pragma Assert (T.C = 0);
   end;

   declare
      S, T : Natural_And_Rec;
   begin
      if E then
         S.C := 0;
         T.C := 0;
      end if;

      ----------------------------------------------------
      -- C might not be and A and B are not initialized --
      ----------------------------------------------------

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ---------------------------------------------------
      -- C and A might not be and B is not initialized --
      ---------------------------------------------------

      if E then
         S.D.A := 0;
      end if;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      -----------------------------------------
      -- C, A and B might not be initialized --
      -----------------------------------------

      if E then
         S.D.B := 0;
      end if;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ---------------------------------------------------------
      -- C might not be, A is and B might not be initialized --
      ---------------------------------------------------------

      S.D.A := 0;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ----------------------------------------------------
      -- C might not be, A is, and B is not initialized --
      ----------------------------------------------------

      T.D.A := 0;

       pragma Assert (T.D.A = T.D.B and T.D.A = T.C);

      pragma Assert (T.D.A = T.D.B);

      pragma Assert (T.D.A = T.C);

      pragma Assert (T.D.A = 0);
      pragma Assert (T.D.B = 0);
      pragma Assert (T.C = 0);
   end;

   declare
      S, T : Natural_And_Rec;
   begin
      S.C := 0;
      T.C := 0;

      --------------------------------------------------
      -- C is initialized, A and B or not initialized --
      --------------------------------------------------

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ---------------------------------------------------
      -- C is, A might not be and B is not initialized --
      ---------------------------------------------------

      if E then
         S.D.A := 0;
      end if;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      ----------------------------------------------
      --  C is, A and B might not be initialized  --
      ----------------------------------------------

      if E then
         S.D.B := 0;
      end if;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      -----------------------------------------------
      --  C and A are, B might not be initialized  --
      -----------------------------------------------

      S.D.A := 0;

      pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

      pragma Assert (S.D.A = S.D.B);

      pragma Assert (S.D.A = S.C);

      pragma Assert (S.D.A = 0);
      pragma Assert (S.D.B = 0);
      pragma Assert (S.C = 0);

      --------------------------------------------
      --  C and A are and B is not initialized  --
      --------------------------------------------

      T.D.A := 0;

       pragma Assert (T.D.A = T.D.B and T.D.A = T.C);

      pragma Assert (T.D.A = T.D.B);

      pragma Assert (T.D.A = T.C);

      pragma Assert (T.D.A = 0);
      pragma Assert (T.D.B = 0);
      pragma Assert (T.C = 0);
   end;

   -----------------------------------------------------------------
   -- The A, B and C fields are used directly after being havoced --
   -----------------------------------------------------------------

   declare
      S : Natural_And_Rec := (0, (0,0));
   begin
      begin
         Raise_Exception (S);
      exception
         when My_Exception =>
            pragma Assert (S.D.A = S.D.B and S.D.A = S.C);

            pragma Assert (S.D.A = S.D.B);

            pragma Assert (S.D.A = S.C);

            pragma Assert (S.D.A = 0);
            pragma Assert (S.D.B = 0);
            pragma Assert (S.C = 0);
      end;
   end;
end Normal_Components;
