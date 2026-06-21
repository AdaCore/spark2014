package body Pkg
  with SPARK_Mode
is
   procedure P (X : Integer) is
   begin
      Sink := X;
   end P;

   procedure P (X : Boolean) is
   begin
      Sink := (if X then 1 else 0);
   end P;

   procedure Q is
   begin
      Sink := 0;
   end Q;

   procedure R (X : Integer) is
   begin
      Sink := X;
   end R;

   package body Inner is
      procedure S (X : Integer) is
      begin
         Sink := X;
      end S;

      function F (X : Integer) return Integer
      is (X);
   end Inner;
end Pkg;
