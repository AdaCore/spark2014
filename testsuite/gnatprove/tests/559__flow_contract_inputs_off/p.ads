package P with SPARK_Mode is

   Outp : Integer := 0;
   Inp  : Integer := 0;
   Both : Integer := 0;

   --  Violations: something read on entry is not an input of the subprogram

   procedure Bad_Pre_Global (X : out Integer)
     with Global => (Output => Outp), Pre => Outp > 0, Post => X = 0;

   procedure Bad_Pre_Formal (X : out Integer)
     with Global => null, Pre => X > 0, Post => X = 1;

   procedure Bad_Old_Global (X : out Integer)
     with Global => (Output => Outp), Post => X = Outp'Old;

   procedure Bad_Old_Formal (X : out Integer)
     with Global => null, Post => X = X'Old;

   --  Legitimate: every one of these reads a genuine input

   procedure Ok_In_Out (X : out Integer)
     with Global => (In_Out => Both), Pre => Both > 0, Post => X = Both;

   procedure Ok_Input (X : out Integer)
     with Global => (Input => Inp), Pre => Inp > 0, Post => X = Inp;

   procedure Ok_Old (X : out Integer)
     with Global => (Input => Inp, In_Out => Both),
          Post => X = Inp'Old + Both'Old;

   --  Absent from the Global contract altogether: reported by
   --  Flow_Sanity.Check_Incomplete_Globals, and not a second time here

   procedure Missing_Global (X : out Integer)
     with Global => null, Pre => Inp > 0, Post => X = 0;

   --  Bounds of an out parameter are well defined on entry

   procedure Ok_Bound (X : out String)
     with Global => null, Pre => X'Length = 10;

end P;
