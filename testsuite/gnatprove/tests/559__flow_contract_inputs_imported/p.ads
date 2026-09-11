--  An imported subprogram has no body, so the contract sanity checks apply
--  to it for the same reason they apply to a body with SPARK_Mode => Off.

package P with SPARK_Mode is

   Outp : Integer := 0;
   Inp  : Integer := 0;
   Both : Integer := 0;

   type T is record
      C : Integer;
   end record;

   --  Violations: something read on entry is not an input of the subprogram

   procedure Bad_Pre_Global (X : out Integer)
     with Global => (Output => Outp), Pre => Outp > 0, Post => X = 0,
          Import, Convention => C;

   procedure Bad_Pre_Formal (X : out Integer)
     with Global => null, Pre => X > 0, Post => X = 1,
          Import, Convention => C;

   procedure Bad_Old_Global (X : out Integer)
     with Global => (Output => Outp), Post => X = Outp'Old,
          Import, Convention => C;

   procedure Bad_Old_Formal (X : out Integer)
     with Global => null, Post => X = X'Old,
          Import, Convention => C;

   function "=" (A, B : T) return Boolean
     with Global => (Input => Inp), Import, Convention => C;

   --  Without a Global contract the formal-mode half still applies

   procedure No_Global_Bad_Formal (X : out Integer)
     with Pre => X > 0, Post => X = 1, Import, Convention => C;

   procedure No_Global_Bad_Old (X : out Integer)
     with Post => X = X'Old, Import, Convention => C;

   --  Legitimate: every one of these reads a genuine input

   procedure Ok_Input (X : out Integer)
     with Global => (Input => Inp), Pre => Inp > 0, Post => X = Inp,
          Import, Convention => C;

   procedure Ok_In_Out (X : out Integer)
     with Global => (In_Out => Both), Pre => Both > 0, Post => X = Both,
          Import, Convention => C;

   procedure Ok_Bound (X : out String)
     with Global => null, Pre => X'Length = 10,
          Import, Convention => C;

end P;
