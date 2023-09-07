with P;  use P;
procedure Ext_Part_Extensions_Visible with SPARK_Mode is
begin
   --  In the following tests, the extension parts are introduced by
   --  Extensions_Visible annotations.

   ------------------------------------------
   -- A record with only an extension part --
   ------------------------------------------

      -------------------------------------------
      -- The extension part is not initialized --
      -------------------------------------------
   declare
      procedure Initialize (R : out Empty) with Extensions_Visible is
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
      procedure Initialize (R : out Empty) with Extensions_Visible is

      begin
         if E then
            Initialize_Empty_Class (Empty'Class (R));
         end if;
      end Initialize;
   begin
      null;
   end;

      ---------------------------------------
      -- The extension part is initialized --
      ---------------------------------------
   declare
      procedure Initialize (R : out Empty) with Extensions_Visible is
      begin
         Initialize_Empty_Class (Empty'Class (R));
      end Initialize;
   begin
      null;
   end;
   ----------------------------------------------------------------------------
   --  A record with a normal part and an extension part. The checks are     --
   --  not compressed because the two parts are used in different vertices.  --
   ----------------------------------------------------------------------------

      ----------------------------------------------------------------
      -- The normal part and the extension part are not initialized --
      ----------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal) with Extensions_Visible is
      begin
         null;
      end Initialize;
   begin
      null;
   end;

      -------------------------------------------------------------------------
      -- The normal part is not, the extension part might not be initialized --
      -------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Rec) with Extensions_Visible is
      begin
         if E then
            Initialize_Rec_Class (Rec'Class (R));
         end if;

         begin
            Raise_Exception (R.A);
         exception
            when My_Exception =>
               null;
         end;
      end Initialize;
   begin
      null;
   end;
      ------------------------------------------------------------------
      -- The normal part is not and the extension part is initialized --
      ------------------------------------------------------------------

   declare
      procedure Initialize (R : out Rec) with Extensions_Visible is
      begin
         Initialize_Rec_Class (Rec'Class (R));

         begin
            Raise_Exception (R.A);
         exception
            when My_Exception =>
               null;
         end;
      end Initialize;
   begin
      null;
   end;

      -------------------------------------------------------------------------
      -- The normal part might not be, the extension part is not initialized --
      -------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal) with Extensions_Visible is
      begin
         if E then
            Initialize_Normal (R);
         end if;
      end Initialize;
   begin
      null;
   end;

      ---------------------------------------------------------------------
      -- The normal part and the extension part might not be initialized --
      ---------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal) with Extensions_Visible is
      begin
         if E then
            Initialize_Normal_Class (Normal'Class (R));
         end if;
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------------
      -- The normal part might not be and the extension part is initialized --
      ------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Rec) with Extensions_Visible is
      begin
         Initialize_Rec_Class (Rec'Class (R));

         begin
            Raise_Exception (R.A);
         exception
            when My_Exception =>
               null;
         end;

         if E then
            R.A.A := 0;
         end if;
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------
      -- The normal part is and the extension part is not initialized --
      ------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal) with Extensions_Visible is
      begin
         Initialize_Normal (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------------------
      -- The normal part is and the extension part might not be initialized --
      ------------------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal) with Extensions_Visible is
      begin
         if E then
            Initialize_Normal_Class (Normal'Class (R));
         end if;

         Initialize_Normal (R);
      end Initialize;
   begin
      null;
   end;

      ------------------------------------------------------------
      -- The normal part and the extension part are initialized --
      ------------------------------------------------------------

   declare
      procedure Initialize (R : out Normal) with Extensions_Visible is
      begin
         Initialize_Normal_Class (Normal'Class (R));
      end Initialize;
   begin
      null;
   end;
end Ext_Part_Extensions_Visible;
