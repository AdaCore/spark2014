package BT.O
is
   type T is private;
   NT : constant T;
   function SF (S : in T) return BT.MyP;
private
   type T is record
      F1 : BT.MyP;
      F2 : BT.MyP;
   end record;
   NT : constant T := T'(1,1);
end BT.O;
