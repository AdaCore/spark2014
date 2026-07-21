package body Pkg
  with SPARK_Mode
is
   procedure R (X : Integer) is
   begin
      Sink := X;
   end R;

   package body Inner is
      procedure S (X : Integer) is
      begin
         Sink := X;
      end S;
   end Inner;
end Pkg;
