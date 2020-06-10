procedure Unsound with SPARK_Mode is

   type T is range 1 .. 100;

   subtype S is T 
      with Dynamic_Predicate => S rem 2 = 0;

   type D is new S;

   function Two return T is (2);
   function Two return D is (2);

   procedure A with Pre => True is
      X : S := Two;
   begin
      X := X + 1;    --@PREDICATE_CHECK:FAIL
   end A;

   procedure B with Pre => True is
      X : D := Two;
   begin
      X := X + 1;    --@PREDICATE_CHECK:FAIL
   end B;

begin
   null;
end Unsound;
