function S (Low, High : Positive) return Boolean
  with Depends => (S'Result => (Low, High)),
       Post    => S'Result = (Low = 1 and High = 3)
is
   subtype T is String (Low .. High);
begin
   return "Foo" in T;
end;
