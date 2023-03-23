package P is
   type T is tagged record
      C : Integer;
   end record;
   type TT is new T with record
      pragma Inspection_Point;
      CC : Integer;
      pragma Inspection_Point;
   end record;
end;
