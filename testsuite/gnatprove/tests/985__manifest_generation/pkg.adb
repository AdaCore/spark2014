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

   function F (X : Integer) return Integer
   is (X);

   function F (X : Boolean) return Integer
   is (if X then 1 else 0);

   procedure Q is
   begin
      Sink := 0;
   end Q;

   package body Inner is
      procedure S (X : Integer) is
      begin
         Sink := X;
      end S;
   end Inner;
end Pkg;
