package P with SPARK_Mode is
   type T is private;
   subtype U is T;
   procedure A (X : T);
   procedure F (X : T);
   procedure G (X : U);
   C : constant T;
private
   type T is access Integer;
   subtype S is T;
   procedure B (X : S);
   C : constant S := new Integer'(0);
   D : constant S := new Integer'(0);
end;
