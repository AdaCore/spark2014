package Object is

   type T is tagged private;

   procedure Create (X : out T);

   procedure Update (X : in out T);

   function Get (X : T) return Integer;

private

   type T is tagged record
      C : Integer;
   end record
     with Type_Invariant => T.C /= 0;

end Object;
