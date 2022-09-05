procedure Neverending_Dispatching with SPARK_Mode,
  Annotate => (GNATprove, Always_Return) is

   package ParentDecl is
      type T is tagged null record;
      function Init return T is (null record);
      function Work(X:T) return Integer;
   end ParentDecl;
   package body ParentDecl is
      function Work(X:T) return Integer is
      begin
         return 0;
      end Work;
   end ParentDecl;
   use ParentDecl;

   package ChildDecl is
      type U is new T with null record;
      function Init return U is (null record);
      function Work(X:U) return Integer;
   end ChildDecl;

   package body ChildDecl is
      function Work(X:U) return Integer is
      begin
         while True loop
            null;
         end loop;
         return 1;
      end Work;
   end ChildDecl;
   use ChildDecl;

   X_0 : U := Init;
   X : T'Class := X_0;
   Y : Integer := Work(X); -- This calls Work defined on U, which is neverending.
begin
   null;
end Neverending_Dispatching;
