package P is

   type Typ (Int : Integer) is record
      null;
   end record;

   package Inst is

      type T is private;

   private
      type T is new Typ (30);

      Null_T : constant T := (Int => 30);
   end;

end;
