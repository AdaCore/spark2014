package My_Types with SPARK_Mode is
   type My_Root is tagged record
      F : Integer;
   end record;

   procedure Incr (X : in out My_Root) with
     Pre        => True,
     Pre'Class  => X.F < Integer'Last,
     Post       => (if X.F'Old < Integer'Last then X.F = X.F'Old + 1),
     Post'Class => X.F = X.F'Old + 1;
end My_Types;
