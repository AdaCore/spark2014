package Dispatch with SPARK_Mode is
   type Root is tagged record
      F : Integer;
   end record;

   function Incr (X : Root) return Root with
     Pre'Class => X.F < Integer'Last,
     Post      => Incr'Result.F = X.F + 1;

   function Incr2 (X : Root) return Root with
     Pre'Class => True,

     Post      => Incr2'Result.F = X.F + 1;

   function Incr3 (X : Root) return Root with
     Pre'Class  => X.F < Integer'Last,

     Post'Class => Incr3'Result.F = X.F + 1,
     Post       => (if X.F'Old < Integer'Last then Incr3'Result.F = X.F + 1);

   function Incr4 (X : Root) return Root with
     Pre'Class  => X.F < Integer'Last,
     Post'Class => Incr4'Result.F = X.F + 1;

   function Incr5 (X : Root) return Root with
     Pre'Class  => X.F < Integer'Last,
     Post       => True, --@STRONGER_POST:FAIL
     Post'Class => Incr5'Result.F = X.F + 1;

   function Incr6 (X : Root) return Root with
     Pre'Class  => X.F < Integer'Last,

     Post'Class => (if X.F'Old < Integer'Last then Incr6'Result.F = X.F + 1),
     Contract_Cases =>
         (X.F < Integer'Last => Incr6'Result.F = X.F + 1,
          others             => Incr6'Result.F = 0);

end Dispatch;
