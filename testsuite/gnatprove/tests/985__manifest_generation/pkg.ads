package Pkg
  with SPARK_Mode
is
   Sink : Integer := 0;

   --  Overloaded procedures, distinguished only by parameter type. The
   --  generated manifest must keep them apart with a profile field whenever it
   --  emits an explicit entry for either of them.
   procedure P (X : Integer)
   with Post => Sink = X;
   procedure P (X : Boolean)
   with Post => Sink = (if X then 1 else 0);

   --  Overloaded functions; a function profile also records the return type.
   function F (X : Integer) return Integer
   with Post => F'Result = X;
   function F (X : Boolean) return Integer
   with Post => F'Result = (if X then 1 else 0);

   --  A non-overloaded subprogram, for contrast.
   procedure Q
   with Post => Sink = 0;

   package Inner
     with SPARK_Mode
   is
      procedure S (X : Integer)
      with Post => Sink = X;
   end Inner;
end Pkg;
