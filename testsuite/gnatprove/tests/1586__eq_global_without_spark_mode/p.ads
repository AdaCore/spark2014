package P is
   G : Boolean := True;

   type T is record
      C : Integer;
   end record;

   function "=" (Left, Right : T) return Boolean
     with Import, Global => (Input => G);
end P;
