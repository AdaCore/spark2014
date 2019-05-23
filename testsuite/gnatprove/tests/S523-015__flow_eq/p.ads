package P is
   type T is record
      null;
   end record;

   function "=" (X, Y : T) return Boolean;
end;
