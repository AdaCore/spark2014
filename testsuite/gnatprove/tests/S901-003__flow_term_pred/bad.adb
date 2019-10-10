procedure Bad is
   function A return Boolean;
   function B return Boolean;

   function A return Boolean is (B);
   function B return Boolean is (A);
   --  Two mutually recursive functions; both non-terminating

   subtype T is Integer with Predicate => A;
   --  Call to a non-terminating function in predicate expression

   function In_T (X : Integer) return Boolean;
   pragma Annotate (GNATprove, Terminating, In_T);
   --  This terminating annotation is incorrect, because there is .

   function In_T (X : Integer) return Boolean is
   begin
      return X in T;
      --  A membership test which evaluates the non-terminating type predicate
      --  on T (flow only detects predicate evaluation via membership tests).
   end In_T;

begin
   null;
end;
