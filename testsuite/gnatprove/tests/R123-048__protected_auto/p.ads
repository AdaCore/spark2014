package P is
   --  The Ravenscar profile restrictions are not active here, so F is not in
   --  SPARK, because the type of its implicit formal parameter (PO, the type)
   --  is not in SPARK (and the explicit actual parameter, PO, the object, is
   --  also not in SPARK).
   protected PO is
      function F return Integer;
   end;
end;
