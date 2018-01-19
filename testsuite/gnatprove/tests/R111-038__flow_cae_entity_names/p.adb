package body P is
   F : Integer with Constant_After_Elaboration;
   G : Integer;

   procedure Foo (X : Integer)
   is
   begin
      G := X;
   end;

   procedure Bar (X : Integer)
   is
   begin
      F := X;
   end;
end;
