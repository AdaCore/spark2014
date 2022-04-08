with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   -- Record without discrimiant

   type Simple_Rec is record
      Field : Integer;
   end record;

   subtype Sub_Simple_Rec_1 is Simple_Rec;

   subtype Sub_Simple_Rec_2 is Simple_Rec;

   procedure Record_Subtype (R : Simple_Rec);

   procedure Record_Subtypes (R : Simple_Rec);


   --  Record with discriminant

   type My_Record (Discr : Integer) is record
      Field : Integer;
   end record;

   subtype My_Sub_Record_42 is My_Record (Discr => 42);

   subtype My_Sub_Record_53 is My_Record (Discr => 53);

   procedure Record_Discr_Same (R : My_Record);

   procedure Record_Discr_Down (R : My_Record);

   procedure Record_Discr_Up (R : My_Sub_Record_42);

   procedure Record_Discr_Different (R : My_Sub_Record_42);

   procedure Record_Discr_Parameter_Good (R : My_Record)
      with Pre => R.Discr = 42;

   function Aux_Record_Discr_Parameter_Bad (R : My_Record) return Boolean;

   procedure Record_Discr_Parameter_Bad (R : My_Sub_Record_42);


   --  Record with discriminant dependent contraint

   type Array_Unconstrained is array (Integer range <>) of Integer;

   type Rec (Index_Min, Index_Max : Integer) is record
      A : Array_Unconstrained (Index_Min .. Index_Max);
   end record;

   subtype Rec_Small is Rec (Index_Min => 1, Index_Max => 3);

   procedure Record_Discr_Constraint_Same (R : Rec);

   procedure Record_Discr_Constraint_Down (R : Rec);

   procedure Record_Discr_Constraint_Up (R : Rec_Small);


   --  Tagged

     type Shape is tagged
         record
           X : Integer;
           Y : Integer;
        end record;

     type Circle is new Shape with
        record
           Radius : Integer;
        end record;

     type Point is new Shape with null record;

     procedure Record_Tagged (S : Shape'Class);


   --  Arrays

   type Array_Constrained is array (1 .. 10) of Integer;

   subtype Sub_Array_Constrained is Array_Constrained;

   subtype Sub_Array_Unconstrained is Array_Unconstrained (1 .. 10);

   subtype Sub_Array_Unconstrained_2 is Array_Unconstrained (1 .. 42);

   procedure Array_Constrained_Same (A : Array_Constrained);

   procedure Array_Constrained_Up (A : Array_Constrained);

   procedure Array_Constrained_Down (A : Array_Constrained);

   procedure Array_Unconstrained_Same (A : Array_Unconstrained);

   procedure Array_Unconstrained_Up
      (A : Sub_Array_Unconstrained);

   procedure Array_Unconstrained_Down (A : Array_Unconstrained);

   procedure Array_Unconstrained_Diff
      (A : Sub_Array_Unconstrained);

   --  Other non-discrete types

   procedure In_Range_Float (X : Float);

   --  Implementations

   --------------------
   -- Record_Subtype --
   --------------------

   procedure Record_Subtype (R : Simple_Rec) is
      Match : Boolean := False;
   begin

      if R in Sub_Simple_Rec_1 then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Subtype;

   ---------------------
   -- Record_Subtypes --
   ---------------------

   procedure Record_Subtypes (R : Simple_Rec) is
      Match : Boolean := False;
   begin

      if R in Sub_Simple_Rec_2 | Sub_Simple_Rec_2 then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Subtypes;

   -----------------------
   -- Record_Discr_Same --
   -----------------------

   procedure Record_Discr_Same (R : My_Record) is
      Match : Boolean := False;
   begin

      if R in My_Record then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Same;

   -----------------------
   -- Record_Discr_Down --
   -----------------------

   procedure Record_Discr_Down (R : My_Record) is
      Match : Boolean := False;
   begin

      if R in My_Sub_Record_42 then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Down;

   ---------------------
   -- Record_Discr_Up --
   ---------------------

   procedure Record_Discr_Up (R : My_Sub_Record_42) is
      Match : Boolean := False;
   begin

      if R in My_Record then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Up;

   ----------------------------
   -- Record_Discr_Different --
   ----------------------------

   procedure Record_Discr_Different (R : My_Sub_Record_42) is
      Match : Boolean := False;
   begin

      if R not in My_Sub_Record_53 then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Different;

   ---------------------------------
   -- Record_Discr_Parameter_Good --
   ---------------------------------

   procedure Record_Discr_Parameter_Good (R : My_Record) is
      Match : Boolean := False;
   begin

      if R in My_Sub_Record_42 then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Parameter_Good;

   ------------------------------------
   -- Aux_Record_Discr_Parameter_Bad --
   ------------------------------------

   function Aux_Record_Discr_Parameter_Bad (R : My_Record) return Boolean is
      Match : Boolean := False;
   begin

      if R in My_Sub_Record_42 then
         Match := True;
      end if;

      return Match;

   end Aux_Record_Discr_Parameter_Bad;

   --------------------------------
   -- Record_Discr_Parameter_Bad --
   --------------------------------

   procedure Record_Discr_Parameter_Bad (R : My_Sub_Record_42) is
      Match : constant Boolean := Aux_Record_Discr_Parameter_Bad (R);
   begin

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Parameter_Bad;

   ----------------------------------
   -- Record_Discr_Constraint_Same --
   ----------------------------------

   procedure Record_Discr_Constraint_Same (R : Rec) is
      Match   : Boolean := False;
   begin

      if R in Rec then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Constraint_Same;

   ----------------------------------
   -- Record_Discr_Constraint_Down --
   ----------------------------------

   procedure Record_Discr_Constraint_Down (R : Rec) is
      Match : Boolean := False;
   begin

      if R in Rec_Small then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Constraint_Down;

   --------------------------------
   -- Record_Discr_Constraint_Up --
   --------------------------------

   procedure Record_Discr_Constraint_Up (R : Rec_Small) is
      Match : Boolean := False;
   begin

      if R in Rec then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Record_Discr_Constraint_Up;

   -------------------
   -- Record_Tagged --
   -------------------

     procedure Record_Tagged (S : Shape'Class) is
        Match : Boolean := False;
     begin

        if S in Circle then
           Match := True;
        end if;

        if Match then
           Put_Line ("Success");
        else
           Put_Line ("Failure");
        end if;

     end Record_Tagged;

   --------------------------
   -- Array_Constrained_Up --
   --------------------------

   procedure Array_Constrained_Same (A : Array_Constrained) is
      Match : Boolean := False;
   begin

      if A in Array_Constrained then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Constrained_Same;

   --------------------------
   -- Array_Constrained_Up --
   --------------------------

   procedure Array_Constrained_Up (A : Sub_Array_Constrained) is
      Match : Boolean := False;
   begin

      if A in Array_Constrained then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Constrained_Up;

   ----------------------------
   -- Array_Constrained_Down --
   ----------------------------

   procedure Array_Constrained_Down (A : Array_Constrained) is
      Match : Boolean := False;
   begin

      if A in Sub_Array_Constrained then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Constrained_Down;

   ------------------------------
   -- Array_Unconstrained_Same --
   ------------------------------

   procedure Array_Unconstrained_Same (A : Array_Unconstrained) is
      Match : Boolean := False;
   begin

      if A in Array_Unconstrained then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Unconstrained_Same;

   ----------------------------
   -- Array_Unconstrained_Up --
   ----------------------------

   procedure Array_Unconstrained_Up (A : Sub_Array_Unconstrained) is
      Match : Boolean := False;
   begin

      if A in Array_Unconstrained then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Unconstrained_Up;

   ------------------------------
   -- Array_Unconstrained_Down --
   ------------------------------

   procedure Array_Unconstrained_Down (A : Array_Unconstrained) is
      Match : Boolean := False;
   begin

      if A in Sub_Array_Unconstrained then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Unconstrained_Down;

   ------------------------------
   -- Array_Unconstrained_Diff --
   ------------------------------

   procedure Array_Unconstrained_Diff (A : Sub_Array_Unconstrained) is
      Match : Boolean := False;
   begin

      if A not in Sub_Array_Unconstrained_2 then
         Match := True;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end Array_Unconstrained_Diff;

   --------------------
   -- In_Range_Float --
   --------------------

   procedure In_Range_Float (X : Float) is
      Match : Boolean := True;
   begin

      if X in 0.5 .. 1.0 then
         Match := False;
      end if;

      if Match then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;

   end In_Range_Float;

   --  Local variables

   Simple_R       : constant Simple_Rec       := (Field => 12);
   Discr_R1       : constant My_Record        := (Discr => 1 , Field => 1 );
   Discr_R2       : constant My_Record        := (Discr => 42, Field => 42);
   Discr_Sub_42   : constant My_Sub_Record_42 := (Discr => 42, Field => 42);
   --  Discr_Constr1  : constant Rec              := (Index_Min => 5,
   --                                                 Index_Max => 8,
   --                                                 A => (others => 1));
   --  Discr_Constr2  : constant Rec              := (Index_Min => 1,
   --                                                 Index_Max => 3,
   --                                                 A => (others => 1));
   --  Discr_Constr3  : constant Rec_Small        := (Index_Min => 1,
   --                                                 Index_Max => 3,
   --                                                 A => (others => 1));
   --  Tag_Circle     : Circle;
   Arr_Constr     : constant Array_Constrained             := (others => 1);
   Sub_Arr_Constr : constant Sub_Array_Constrained         := (others => 1);
   Arr_Unconstr1  : constant Array_Unconstrained (5 .. 8)  := (others => 1);
   Arr_Unconstr2  : constant Array_Unconstrained (1 .. 10) := (others => 1);
   Sub_Arr_UC     : constant Sub_Array_Unconstrained       := (others => 1);

begin

   --  The commented tests pertain to features that are not implemented yet.
   --  Once they are the corresponding lines should be uncommented and the
   --  execution should succeed.

   Put_Line ("Record_Subtype");
   Record_Subtype (Simple_R);
   Put_Line ("");

   Put_Line ("Record_Subtypes");
   Record_Subtypes (Simple_R);
   Put_Line ("");

   Put_Line ("Record_Discr_Same");
   Record_Discr_Same (Discr_R1);
   Put_Line ("");

   Put_Line ("Record_Discr_Down");
   Record_Discr_Down (Discr_R2);
   Put_Line ("");

   Put_Line ("Record_Discr_Up");
   Record_Discr_Up (Discr_Sub_42);
   Put_Line ("");

   Put_Line ("Record_Discr_Different");
   Record_Discr_Different (Discr_Sub_42);
   Put_Line ("");

   Put_Line ("Record_Discr_Parameter_Good");
   Record_Discr_Parameter_Good (Discr_R2);
   Put_Line ("");

   Put_Line ("Record_Discr_Parameter_Bad");
   Record_Discr_Parameter_Bad (Discr_Sub_42);
   Put_Line ("");

   Put_Line ("Record_Discr_Constraint_Same");
   Put_Line ("Unsupported record with discriminant dependant component");
   --  Record_Discr_Constraint_Same (Discr_Constr1);
   Put_Line ("");

   Put_Line ("Record_Discr_Constraint_Down");
   Put_Line ("Unsupported record with discriminant dependant component");
   --  Record_Discr_Constraint_Down (Discr_Constr2);
   Put_Line ("");

   Put_Line ("Record_Discr_Constraint_Up");
   Put_Line ("Unsupported record with discriminant dependant component");
   --  Record_Discr_Constraint_Up (Discr_Constr3);
   Put_Line ("");

   Put_Line ("Record_Tagged");
   Put_Line ("Unsupported tagged types");
   --  Record_Tagged (Tag_Circle);
   Put_Line ("");

   Put_Line ("Array_Constrained_Same");
   Array_Constrained_Same (Arr_Constr);
   Put_Line ("");

   Put_Line ("Array_Constrained_Up");
   Array_Constrained_Up (Sub_Arr_Constr);
   Put_Line ("");

   Put_Line ("Array_Constrained_Down");
   Array_Constrained_Down (Arr_Constr);
   Put_Line ("");

   Put_Line ("Array_Unconstrained_Same");
   Array_Unconstrained_Same (Arr_Unconstr1);
   Put_Line ("");

   Put_Line ("Array_Unconstrained_Up");
   Array_Unconstrained_Up (Sub_Arr_UC);
   Put_Line ("");

   Put_Line ("Array_Unconstrained_Down");
   Array_Unconstrained_Down (Arr_Unconstr2);
   Put_Line ("");

   Put_Line ("Array_Unconstrained_Diff");
   Array_Unconstrained_Diff (Sub_Arr_UC);
   Put_Line ("");

   Put_Line ("In_Range_Float");
   Put_Line ("Unsupported real types");
   --  In_Range_Float (0.7);

end Main;
