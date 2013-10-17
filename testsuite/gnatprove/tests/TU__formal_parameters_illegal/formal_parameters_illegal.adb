package body Formal_Parameters_Illegal
  with SPARK_Mode
is
   type Record_T is record
      A, B : Integer;
   end record;

   type Array_T is array (1 .. 10) of Integer;

   procedure Formal_Not_Fully_Initialized (Rec : out Record_T) is
     --  TU: 1. A subprogram formal parameter of a composite type which is
     --  updated but not fully initialized by the subprogram shall have a mode
     --  of **in out**.
   begin
      Rec.A := 5;
   end Formal_Not_Fully_Initialized;

   procedure Out_Formal_Read_Before_Initialized (Arr : out Array_T)
     --  TU: 2. A subprogram formal parameter of mode **out** shall not be read
     --  by the subprogram until it has been updated by the subprogram. The use
     --  of a discriminant or an attribute related to a property, not its
     --  value, of the formal parameter is not considered to be a read of the
     --  formal parameter. [Examples of attributes that may be used are
     --  A'First, A'Last and A'Length; examples of attributes that are
     --  dependent on the value of the formal parameter and shall not be used
     --  are X'Old and X'Update.]
     with Post => Arr (2) = Arr'Old (2)
   is
   begin
      Arr := Arr'Update (5 => 5);
   end Out_Formal_Read_Before_Initialized;
end Formal_Parameters_Illegal;
