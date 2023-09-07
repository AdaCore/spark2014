with P;  use P;

procedure Ext_Part_Classwide with SPARK_Mode is
begin
   --  In the following tests, the extension parts come from classwide
   --  variables.

   ------------------------------------------
   -- A record with only an extension part --
   ------------------------------------------

      -------------------------------------------
      -- The extension part is not initialized --
      -------------------------------------------
   declare
      procedure Initialize (R : out Empty'Class) is
      begin
         null;
      end Initialize;
   begin
     null;
   end;

      --------------------------------------------------
      --  The extension part might not be initialized --
      --------------------------------------------------
   declare
      procedure Initialize (R : out Empty'Class) is
      begin
         if E then
            Initialize_Empty_Class (R);
         end if;
      end Initialize;
   begin
      null;
   end;

      ---------------------------------------
      -- The extension part is initialized --
      ---------------------------------------
   declare
      procedure Initialize (R : out Empty'Class) is
      begin
         Initialize_Empty_Class (R);
      end Initialize;
   begin
      null;
   end;

   -------------------------------------------------------
   -- A record with a normal part and an extension part --
   -------------------------------------------------------

      ----------------------------------------------------------------
      -- The normal part and the extension part are not initialized --
      ----------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal'Class) is
      begin
         pragma Assert (R = R);
         Initialize_Normal_Class (R);
      end Initialize;
   begin
      null;
   end;

      -------------------------------------------------------------------------
      -- The normal part is not, the extension part might not be initialized --
      -------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Rec'Class) is
      begin
         if E then
            Initialize_Rec_Class (R);
         end if;

         begin
            Raise_Exception (R.A);
         exception
            when My_Exception =>
               pragma Assert (R = R);
         end;

         Initialize_Rec_Class (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------
      -- The normal part is not and the extension part is initialized --
      ------------------------------------------------------------------

   declare
      procedure Initialize (R : out Rec'Class) is
      begin
         Initialize_Rec_Class (R);

         begin
            Raise_Exception (R.A);
         exception
            when My_Exception =>
               pragma Assert (R = R);
         end;

         Initialize_Rec_Class (R);
      end Initialize;
   begin
      null;
   end;

      -------------------------------------------------------------------------
      -- The normal part might not be, the extension part is not initialized --
      -------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal'Class) is
      begin
         if E then
            Initialize_Normal (Normal (R));
         end if;

         pragma Assert (R = R);
         Initialize_Normal_Class (R);
      end Initialize;
   begin
      null;
   end;

      ---------------------------------------------------------------------
      -- The normal part and the extension part might not be initialized --
      ---------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal'Class) is
      begin
         if E then
            Initialize_Normal_Class (R);
         end if;

         pragma Assert (R = R);
         Initialize_Normal_Class (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------------
      -- The normal part might not be and the extension part is initialized --
      ------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Rec'Class) is
      begin
         Initialize_Rec_Class (R);

         begin
            Raise_Exception (R.A);
         exception
            when My_Exception =>
               null;
         end;

         if E then
            R.A.A := 0;
         end if;

         pragma Assert (R = R);
         Initialize_Rec_Class (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------
      -- The normal part is and the extension part is not initialized --
      ------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal'Class) is
      begin
         Initialize_Normal (Normal (R));
         pragma Assert (R = R);
         Initialize_Normal_Class (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------------
      -- The normal part is and the extension part might not be initialized --
      ------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal'Class) is
      begin
         if E then
            Initialize_Normal_Class (R);
         end if;

         Initialize_Normal (Normal (R));
         pragma Assert (R = R);
         Initialize_Normal_Class (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------
      -- The normal part and the extension part are initialized --
      ------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal'Class) is
      begin
         Initialize_Normal_Class (R);
         pragma Assert (R = R);
      end Initialize;
   begin
      null;
   end;
end Ext_Part_Classwide;
