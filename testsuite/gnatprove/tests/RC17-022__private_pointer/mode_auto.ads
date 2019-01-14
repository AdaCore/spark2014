package Mode_Auto is
   type T is private;
   function Is_Null (X : T) return Boolean;
   C : constant T;
   D : constant T;
private
   type T is access Integer;
   function Is_Null (X : T) return Boolean is (X = null);
   C : constant T := new Integer'(3);
   D : constant T := null;
end Mode_Auto;
