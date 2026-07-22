package body Pkg
  with SPARK_Mode
is
   procedure Set (X : Integer) is
      --  A pair of overloads nested inside the Integer overload of Set. Each is
      --  told apart from its sibling only by its profile, exactly like the
      --  outer Set overloads, but one level deeper.

      procedure Helper (A : Integer)
      with Post => Sink = A;

      procedure Helper (A : Boolean)
      with Post => Sink = (if A then 1 else 0);

      procedure Helper (A : Integer) is
      begin
         Sink := A;
      end Helper;

      procedure Helper (A : Boolean) is
      begin
         Sink := (if A then 1 else 0);
      end Helper;

   begin
      if X >= 0 then
         Helper (X);
      else
         Helper (True);
      end if;
   end Set;

   procedure Set (X : Boolean) is
   begin
      Sink := (if X then 1 else 0);
   end Set;
end Pkg;
