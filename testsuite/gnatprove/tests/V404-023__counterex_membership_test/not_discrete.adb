package body Not_Discrete is

   --------------------
   -- Record_Subtype --
   --------------------

   function Record_Subtype (R : Simple_Rec) return Boolean is
      Is_Sub : Boolean := False;
   begin

      if R in Sub_Simple_Rec_1 then
         Is_Sub := True;
      end if;

      pragma Assert (not Is_Sub);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Sub;
   end Record_Subtype;

   ---------------------
   -- Record_Subtypes --
   ---------------------

   function Record_Subtypes (R : Simple_Rec) return Boolean is
      Is_Sub : Boolean := False;
   begin

      if R in Sub_Simple_Rec_1 | Sub_Simple_Rec_2 then
         Is_Sub := True;
      end if;

      pragma Assert (not Is_Sub);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Sub;
   end Record_Subtypes;

   -----------------------
   -- Record_Discr_Same --
   -----------------------

   function Record_Discr_Same (R : My_Record) return Boolean is
      Is_Rec   : Boolean := False;
   begin

      if R in My_Record then
         Is_Rec := True;
      end if;

      pragma Assert (not Is_Rec);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Rec;
   end Record_Discr_Same;

   -----------------------
   -- Record_Discr_Down --
   -----------------------

   function Record_Discr_Down (R : My_Record) return Boolean is
      Is_Small : Boolean := False;
   begin

      if R in My_Sub_Record_42 then
         Is_Small := True;
      end if;

      pragma Assert (not Is_Small);  --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Small;
   end Record_Discr_Down;

   ---------------------
   -- Record_Discr_Up --
   ---------------------

   function Record_Discr_Up (R : My_Sub_Record_42) return Boolean is
      Is_Rec : Boolean := False;
   begin

      if R in My_Record then
         Is_Rec := True;
      end if;

      pragma Assert (not Is_Rec);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Rec;
   end Record_Discr_Up;

   ----------------------------
   -- Record_Discr_Different --
   ----------------------------

   function Record_Discr_Different (R : My_Sub_Record_42) return Boolean is
      Is_Rec : Boolean := False;
   begin

      if R not in My_Sub_Record_53 then
         Is_Rec := True;
      end if;

      pragma Assert (not Is_Rec);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Rec;
   end Record_Discr_Different;

   ---------------------------------
   -- Record_Discr_Parameter_Good --
   ---------------------------------

   function Record_Discr_Parameter_Good (R : My_Record) return Boolean is
      Is_Sub_42 : Boolean := False;
   begin

      if R in My_Sub_Record_42 then
         Is_Sub_42 := True;
      end if;

      pragma Assert (not Is_Sub_42); --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Sub_42;
   end Record_Discr_Parameter_Good;

   ------------------------------------
   -- Aux_Record_Discr_Parameter_Bad --
   ------------------------------------

   function Aux_Record_Discr_Parameter_Bad (R : My_Record) return Boolean is
      Is_Sub_42 : Boolean := False;
   begin

      if R in My_Sub_Record_42 then
         Is_Sub_42 := True;
      end if;


      return Is_Sub_42;
   end Aux_Record_Discr_Parameter_Bad;

   --------------------------------
   -- Record_Discr_Parameter_Bad --
   --------------------------------

   function Record_Discr_Parameter_Bad (R : My_Sub_Record_42) return Boolean is
      B : constant Boolean := Aux_Record_Discr_Parameter_Bad (R);
   begin
      pragma Assert (B);             --  @ASSERT:FAIL @COUNTEREXAMPLE
      return B;
   end Record_Discr_Parameter_Bad;

   -----------------------
   -- Record_Discr_Same --
   -----------------------

   function Record_Discr_Constraint_Same (R : Rec) return Boolean is
      Is_Rec   : Boolean := False;
   begin

      if R in Rec then
         Is_Rec := True;
      end if;

      pragma Assert (not Is_Rec);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Rec;
   end Record_Discr_Constraint_Same;

   ----------------------------------
   -- Record_Discr_Constraint_Down --
   ----------------------------------

   function Record_Discr_Constraint_Down (R : Rec) return Boolean is
      Is_Small : Boolean := False;
   begin

      if R in Rec_Small then
         Is_Small := True;
      end if;

      pragma Assert (not Is_Small);  --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Small;
   end Record_Discr_Constraint_Down;

   --------------------------------
   -- Record_Discr_Constraint_Up --
   --------------------------------

   function Record_Discr_Constraint_Up (R : Rec_Small) return Boolean is
      Is_Rec : Boolean := False;
   begin

      if R in Rec then
         Is_Rec := True;
      end if;

      pragma Assert (not Is_Rec);    --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Rec;
   end Record_Discr_Constraint_Up;

   -------------------
   -- Record_Tagged --
   -------------------

   function Record_Tagged (S : Shape'Class) return Boolean is
      Is_Circle : Boolean := False;
   begin

      if S in Circle then
         Is_Circle := True;
      end if;

      pragma Assert (not Is_Circle); --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Circle;
   end Record_Tagged;

   ----------------------------
   -- Array_Constrained_Same --
   ----------------------------

   function Array_Constrained_Same (A : Array_Constrained) return Boolean is
      Is_Same : Boolean := False;
   begin

      if A in Array_Constrained then
         Is_Same := True;
      end if;

      pragma Assert (not Is_Same);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Same;
   end Array_Constrained_Same;

   --------------------------
   -- Array_Constrained_Up --
   --------------------------

   function Array_Constrained_Up (A : Sub_Array_Constrained) return Boolean is
      Is_Up : Boolean := False;
   begin

      if A in Array_Constrained then
         Is_Up := True;
      end if;

      pragma Assert (not Is_Up);     --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Up;
   end Array_Constrained_Up;

   ----------------------------
   -- Array_Constrained_Down --
   ----------------------------

   function Array_Constrained_Down (A : Array_Constrained) return Boolean is
      Is_Down : Boolean := False;
   begin

      if A in Sub_Array_Constrained then
         Is_Down := True;
      end if;

      pragma Assert (not Is_Down);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Down;
   end Array_Constrained_Down;

   ------------------------------
   -- Array_Unconstrained_Same --
   ------------------------------

   function Array_Unconstrained_Same (A : Array_Unconstrained) return Boolean
   is
      Is_Same : Boolean := False;
   begin

      if A in Array_Unconstrained then
         Is_Same := True;
      end if;

      pragma Assert (not Is_Same);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Same;
   end Array_Unconstrained_Same;

   ----------------------------
   -- Array_Unconstrained_Up --
   ----------------------------

   function Array_Unconstrained_Up (A : Sub_Array_Unconstrained) return Boolean
   is
      Is_Up : Boolean := False;
   begin

      if A in Array_Unconstrained then
         Is_Up := True;
      end if;

      pragma Assert (not Is_Up);     --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Up;
   end Array_Unconstrained_Up;

   ------------------------------
   -- Array_Unconstrained_Down --
   ------------------------------

   function Array_Unconstrained_Down (A : Array_Unconstrained) return Boolean
   is
      Is_Up : Boolean := False;
   begin

      if A in Sub_Array_Unconstrained then
         Is_Up := True;
      end if;

      pragma Assert (not Is_Up);     --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Up;
   end Array_Unconstrained_Down;

   ------------------------------
   -- Array_Unconstrained_Diff --
   ------------------------------

   function Array_Unconstrained_Diff (A : Sub_Array_Unconstrained) return Boolean
   is
      Is_Diff : Boolean := False;
   begin

      if A not in Sub_Array_Unconstrained_2 then
         Is_Diff := True;
      end if;

      pragma Assert (not Is_Diff);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Is_Diff;
   end Array_Unconstrained_Diff;

   --------------------
   -- In_Range_Float --
   --------------------

   function In_Range_Float (X : Float) return Boolean is
      B : Boolean := True;
   begin

      if X in 0.5 .. 1.0 then
         B := False;
      end if;

      pragma Assert (B);             --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end In_Range_Float;

end Not_Discrete;
