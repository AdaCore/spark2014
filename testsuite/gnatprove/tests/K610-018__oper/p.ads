package P is
   type T is new Integer;
   function "<"  (Left, Right : T) return Boolean; -- is (True);
   pragma Import (Intrinsic, "<");
   function Compare (Left, Right : T) return Boolean
     with pre => Left < Right;
   function Compare (Left, Right : T) return Boolean is (Left = Right);
end;
