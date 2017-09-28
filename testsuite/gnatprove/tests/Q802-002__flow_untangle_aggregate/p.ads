package P is

   type Typ (Int : Integer) is record
      null;
   end record;

   generic
     Int : Integer;
   package Gen
   is
      Max : Integer := Int;
      type T is private;

      Null_T : constant T;

   private
      type T is new Typ (Max);

      Null_T : constant T := (Int => Max);
   end;

   package Inst is new P.Gen (30);
end;
