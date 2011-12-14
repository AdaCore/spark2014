package P is
   type T is private;
   procedure Bad (V : in out T);
private
   type T is record
      Access_Count : Natural := 0;
      Locked       : Boolean := False;
   end record with
     Predicate => (T.Locked = (T.Access_Count > 3));
end P;
