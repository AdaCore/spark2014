package P is

   type Typ (Int : Integer) is record
      null;
   end record;

   package Inst is
      Max : Integer := 30;

      type T is private;

      Null_T : constant T;

   private
      type T is new Typ (Max);

      Null_T : constant T := (Int => Max);
   end;

end;
