package P is

   Ptr : access function return Integer;

   function Id (Arg : Integer) return Integer;

   X : Integer := Id (Ptr.all);

end;
