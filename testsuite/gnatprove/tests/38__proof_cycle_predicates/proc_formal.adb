procedure Proc_Formal with SPARK_Mode is
   type T is new Integer;

   function F (X : T) return Boolean with Pre => True, Post => False;

   subtype S is T with Predicate => F (S);

   procedure G (X : S) with Pre => True;

   procedure G (X : S) is begin null; end;

   function F (X : T) return Boolean is
   begin
      G (X);
      return True;
   end;

begin
   null;
end;
