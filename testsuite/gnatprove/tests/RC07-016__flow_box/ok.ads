package OK is
   type R is record
      C0 : Integer := 0;
   end record;

   type T is record
      C1 : R;
      C2 : Integer;
   end record;

   X : T := (C1 => <>, C2 => 0);
end;
