package P is
   type T is new Integer;
   function "<"  (Left, Right : T) return Boolean;
   pragma Import (Ada, "<");

   function Compare (Left, Right : T) return Boolean
     with Post => (if Compare'Result then not (Left = Right));

   function Compare (Left, Right : T) return Boolean is
      (Left < Right);
end;
