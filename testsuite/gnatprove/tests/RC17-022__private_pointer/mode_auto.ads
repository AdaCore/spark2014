package Mode_Auto is
   type T is private;
   function Is_Null (X : T) return Boolean with Global => null;
   function "=" (X, Y : T) return Boolean with Global => null;
   C : constant T;
   D : constant T;
private
   type S is access Integer;
   type T is new S;
   function Is_Null (X : T) return Boolean is (S (X) = null);
   function "=" (X, Y : T) return Boolean is
     (Is_Null (X) = Is_Null (Y)
      and then (if not Is_Null (X) then X.all = Y.all));
   C : constant T := new Integer'(3);
   D : constant T := null;
end Mode_Auto;
