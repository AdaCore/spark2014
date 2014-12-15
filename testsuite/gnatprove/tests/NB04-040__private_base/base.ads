package Base with
  SPARK_Mode
is
   type T is tagged private;

   function Sum (X : T) return Integer;

   function Create (C : Integer) return T with
     Post => Sum (Create'Result) = C;

private
   type T is tagged record
      C : Integer;
   end record;

   function Sum (X : T) return Integer is (X.C);

   function Create (C : Integer) return T is (T'(C => C));

end Base;
