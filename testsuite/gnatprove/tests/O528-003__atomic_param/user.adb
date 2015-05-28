with Atomic_Counter; use Atomic_Counter;
procedure User
  with SPARK_Mode
is
   X : Integer := 0;
begin
   X := X + X;
end User;
