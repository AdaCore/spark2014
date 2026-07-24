package body Pkg
  with SPARK_Mode
is
   procedure Set (X : Integer) is
      --  Helper nested in the Integer overload of Set.
      procedure Helper (A : Integer)
      with Post => Sink = A;

      procedure Helper (A : Integer) is
      begin
         Sink := A;
      end Helper;

   begin
      if X >= 0 then
         Helper (X);
      else
         Helper (0);
      end if;
   end Set;

   procedure Set (X : Boolean) is
      --  A same-named, same-profile Helper nested in the Boolean overload of
      --  Set. Its dotted path is identical to the one above.
      procedure Helper (A : Integer)
      with Post => Sink = A;

      procedure Helper (A : Integer) is
      begin
         Sink := A;
      end Helper;

   begin
      Helper (if X then 1 else 0);
   end Set;
end Pkg;
