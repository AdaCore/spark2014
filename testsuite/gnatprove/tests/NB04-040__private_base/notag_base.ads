package Notag_Base with
  SPARK_Mode
is
   type T is private;

   function Sum (X : T) return Integer;

   function Create (C : Integer) return T with
     Post => Sum (Create'Result) = C;

private
   type T is record
      C : Integer;
   end record;

   function Sum (X : T) return Integer is (X.C);

   function Create (C : Integer) return T is (T'(C => C));

end Notag_Base;
