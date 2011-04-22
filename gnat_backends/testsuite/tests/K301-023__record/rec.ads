package Rec is

   type Counter is record
      Count : Positive;
   end record;

   function Next (X : Counter) return Positive
     with Pre  => (X.Count <= 10000),
          Post => (Next'Result = X.Count + 1);

end Rec;
