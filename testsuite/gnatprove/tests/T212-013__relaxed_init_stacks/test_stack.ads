package Test_Stack with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type My_Stack (Max : Natural) is private with
     Default_Initial_Condition => Size (My_Stack) = 0;

   function Size (S : My_Stack) return Natural with Ghost;
   function Peek (S : My_Stack; I : Positive) return Integer with
     Ghost,
     Pre => I in 1 .. Size (S);
   function Bad_Peek (S : My_Stack; I : Positive) return Integer with
     Ghost,
     Pre => I in 1 .. S.Max;

   procedure Push (S : in out My_Stack; E : Integer) with
     Pre  => Size (S) < S.Max,
     Post => Size (S) = Size (S)'Old + 1
     and then Peek (S, Size (S)) = E
     and then (for all K in 1 .. Size (S)'Old => Peek (S, K) = Peek (S'Old, K));

   procedure Bad_Push (S : in out My_Stack; E : Integer) with
     Pre  => Size (S) < S.Max;

   procedure Pop (S : in out My_Stack; E : out Integer) with
     Pre  => Size (S) > 0,
     Post => Size (S) = Size (S)'Old - 1
     and then Peek (S, Size (S))'Old = E
     and then (for all K in 1 .. Size (S) => Peek (S, K) = Peek (S'Old, K));
private
   type Content_Arr is array (Positive range <>) of Integer with
     Relaxed_Initialization;
   type My_Stack (Max : Natural) is record -- I think no flow errors should be reported here
      Top     : Natural := 0;
      Content : Content_Arr (1 .. Max);
   end record
     with Predicate => Top <= Max
     and then (for all K in 1 .. Top => Content (K)'Initialized);

   function Size (S : My_Stack) return Natural is (S.Top);
   function Peek (S : My_Stack; I : Positive) return Integer is
     (S.Content (I)); --@INIT_BY_PROOF:PASS
   function Bad_Peek (S : My_Stack; I : Positive) return Integer is
     (S.Content (I)); --@INIT_BY_PROOF:FAIL
end;
