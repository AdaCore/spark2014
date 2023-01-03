package P is
   type T is abstract tagged record
      C : Integer;
   end record;

   procedure A (X : T) is abstract with Global => null;
   procedure B (X : T) is abstract with Depends => null;
end;
