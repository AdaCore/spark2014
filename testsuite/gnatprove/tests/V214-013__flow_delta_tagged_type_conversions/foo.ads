package Foo with SPARK_Mode is
   type Object is tagged null record;

   type Child is new Object with record
      X : Integer;
   end record;

   function Create (I : Integer) return Object'Class is (Child'(X => I));

   procedure Bar (I : Integer) with
     Post => Object'Class ((Child (Create (I)) with delta X => I)) = Create (I);
end Foo;
