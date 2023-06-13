package termination_explanations_and_fixes with SPARK_Mode is

   procedure Nullify (X : in out Natural)
     with Annotate => (GNATprove, Always_Return);
   --  Procedure containing a loop that might lack a loop variant in its body

   type Acc_To_F is access function return Natural;
   function F return Natural is (0);
   Y : Natural := 0;

   procedure Use_Acc_To_F
     with Annotate => (GNATprove, Always_Return);
   --  Procedure dereferencing an access-to-function, which might hide
   --  recursive calls.

   type Acc_To_P is access procedure;
   procedure P;
   procedure Use_Acc_To_P
     with Annotate => (GNATprove, Always_Return);
   --  Procedure dereferencing an access-to-procedure, in which case it is
   --  useless to report the possible presence of recursive calls.

   type Tagged_Natural is tagged record
      E : Natural;
   end record;
   function Dispatching_F (X : in Tagged_Natural) return Natural;
   procedure Dispatching_P (X : out Tagged_Natural);
   Z : Tagged_Natural'Class := Tagged_Natural'(E => 0);

   procedure Use_Dispatching_F
     with Annotate => (GNATprove, Always_Return);
   --  Procedure making a dispatching call to a function, which might hide
   --  recursive calls.

   procedure Use_Dispatching_P
     with Annotate => (GNATprove, Always_Return);
   --  Procedure making a dispatching call to a procedure, in which case it is
   --  useless to report the possible presence of recursive calls.

   function F_Rec (X : Natural) return Natural;
   --  Recursive function that might lack a Subprogram_Variant aspect

   function A (X : Natural) return Natural;
   function B (X : Natural) return Natural;
   --  Two mutually recursive functions that might lack Subprogram_Variant
   --  aspects.

   function F_Caller return Natural;
   procedure P_Callee;
   --  Procedure that might lack an Always_Return annotation

end termination_explanations_and_fixes;
