package Types is pragma Elaborate_Body;

   type T1 is tagged record J : Integer; end record;
   function Check (X : T1) return Boolean is (True);
   procedure Upd (X : in out T1) with
     Post'Class => Check (X);

   type T2 is new T1 with null record;
   function Check (X : T2) return Boolean is (False);
   procedure Upd (X : in out T2);

end Types;
