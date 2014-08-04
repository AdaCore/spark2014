package More_Specs
  with SPARK_Mode
is
   type Stack_Pointer is range 0 .. 100;
   subtype Index is Stack_Pointer range 1 .. Stack_Pointer'Last;
   type Vector is array (Index) of Natural;

   --  The post conditions of the following subprograms are all
   --  incorrect. The first two may cause a run-time exception in any
   --  mode chosen for the evaluation of assertion expressions. The
   --  last postcondition will always be false when N /= Natural'Last.

   function Min_Element (V : Vector) return Natural with
     Post => (for all N in Stack_Pointer => Min_Element'Result <= V (N));

   procedure Div_Rem (N, D : in Natural; Q , R : out Natural) with
     Post => Q = N / D and R = N - Q * D;

   procedure Increment (N : in out Natural) with
     Post => (if N < Natural'Last then N = N + 1 else N = Natural'Last);
end More_Specs;
