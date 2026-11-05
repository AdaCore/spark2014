package Test with SPARK_Mode is
   package P is
      type Root is record
         F : Integer;
      end record;

      type Derived is private;

      type Positive_Root is record
         F : Positive;
      end record;

      type Positive_Derived is private;
   private
      type Derived is new Root with
        Type_Invariant => Derived.F > 0;

      type Positive_Derived is new Positive_Root with
        Type_Invariant => Positive_Derived.F = 1;
   end P;

   --  Reject invariants declared on the derived record itself, including
   --  when its components have no invalid representations.

   X : P.Derived with Import, Potentially_Invalid;
   Y : P.Positive_Derived with Import, Potentially_Invalid;

   subtype S is P.Derived;
   Z : S with Import, Potentially_Invalid;

   --  Also reject inherited invariants and invariants on nested components.

   type Child is new P.Derived;
   C : Child with Import, Potentially_Invalid;

   type Rec is record
      F : P.Derived;
   end record;
   R : Rec with Import, Potentially_Invalid;

   type Arr is array (1 .. 2) of P.Derived;
   A : Arr with Import, Potentially_Invalid;

   --  The same restriction applies to parameters and function results.

   procedure Proc (Arg : P.Derived) with
     Import, Potentially_Invalid => Arg;

   function Func return P.Derived with
     Import, Potentially_Invalid => Func'Result;
end Test;
