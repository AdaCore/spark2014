package Not_Discrete is

   -- Record without discrimiant

   type Simple_Rec is record
     Field : Integer;
   end record;

   subtype Sub_Simple_Rec_1 is Simple_Rec;

   subtype Sub_Simple_Rec_2 is Simple_Rec;

   function Record_Subtype (R : Simple_Rec) return Boolean;

   function Record_Subtypes (R : Simple_Rec) return Boolean;


   --  Record with discriminant

   type My_Record (Discr : Integer) is record
      Field : Integer := 42;
   end record;

   subtype My_Sub_Record_42 is My_Record (Discr => 42);

   subtype My_Sub_Record_53 is My_Record (Discr => 53);

   function Record_Discr_Same (R : My_Record) return Boolean;

   function Record_Discr_Down (R : My_Record) return Boolean;

   function Record_Discr_Up (R : My_Sub_Record_42) return Boolean;

   function Record_Discr_Different (R : My_Sub_Record_42) return Boolean;

   function Record_Discr_Parameter_Good (R : My_Record) return Boolean
      with Pre => R.Discr = 42;

   function Aux_Record_Discr_Parameter_Bad (R : My_Record) return Boolean;

   function Record_Discr_Parameter_Bad (R : My_Sub_Record_42) return Boolean;

   --  Record with discriminant dependent contraint

   type Array_Unconstrained is array (Integer range <>) of Integer;

   type Rec (Index_Min, Index_Max : Integer) is record
      A : Array_Unconstrained (Index_Min .. Index_Max);
   end record;

   subtype Rec_Small is Rec (Index_Min => 1, Index_Max => 3);

   function Record_Discr_Constraint_Same (R : Rec) return Boolean;

   function Record_Discr_Constraint_Down (R : Rec) return Boolean;

   function Record_Discr_Constraint_Up (R : Rec_Small) return Boolean;


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

   function Record_Tagged (S : Shape'Class) return Boolean;


   --  Arrays

   type Array_Constrained is array (1 .. 10) of Integer;

   subtype Sub_Array_Constrained is Array_Constrained;

   subtype Sub_Array_Unconstrained is Array_Unconstrained (1 .. 10);

   subtype Sub_Array_Unconstrained_2 is Array_Unconstrained (1 .. 42);

   function Array_Constrained_Same (A : Array_Constrained) return Boolean;

   function Array_Constrained_Up (A : Sub_Array_Constrained) return Boolean;

   function Array_Constrained_Down (A : Array_Constrained) return Boolean;

   function Array_Unconstrained_Same (A : Array_Unconstrained) return Boolean;

   function Array_Unconstrained_Up
      (A : Sub_Array_Unconstrained) return Boolean;

   function Array_Unconstrained_Down (A : Array_Unconstrained) return Boolean;

   function Array_Unconstrained_Diff
      (A : Sub_Array_Unconstrained) return Boolean;

   --  Other non-discrete types

   function In_Range_Float (X : Float) return Boolean;

end Not_Discrete;
