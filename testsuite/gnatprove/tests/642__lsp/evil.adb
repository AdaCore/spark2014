procedure Evil with SPARK_Mode is
   package A is
      type T is tagged null record;
      function Ok (X : T) return Boolean is (True);
      procedure P (X : T) is null with Post'Class => Ok (X);
      type U is new T with null record;
      function Ok2 (X : U) return Boolean is (True);
      overriding procedure P (X : U) is null with Post'Class => Ok2 (X); --@STRONGER_CLASSWIDE_POST:FAIL
      type V is new U with null record;
      overriding function Ok (X : V) return Boolean is (False);
      overriding procedure P (X : V) is null;
   end A;

   package B is
      type T is tagged null record;
      function Ok (X : T) return Boolean is (True);
      procedure P (X : T) is null with Post'Class => Ok (X);
      type U is new T with null record;
      function Ok2 (X : U) return Boolean is (True) with
        Post'Class => (if Ok2'Result then Ok (X)); --@POSTCONDITION:FAIL
      overriding procedure P (X : U) is null with Post'Class => Ok2 (X);
      type V is new U with null record;
      overriding function Ok (X : V) return Boolean is (False);
      overriding function Ok2 (X : V) return Boolean is (True);
      overriding procedure P (X : V) is null;
   end B;

   X : A.T'Class := A.V'(null record);
begin
   X.P; --  ASSERTION_ERROR at runtime.
   pragma Assert (False);
end Evil;
