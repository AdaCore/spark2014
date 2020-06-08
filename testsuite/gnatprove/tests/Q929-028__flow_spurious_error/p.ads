package P with Elaborate_Body
is
   type Typ (Int : Integer) is record
      null;
   end record;

   package Inst with
      Abstract_State => State,
      Initializes => (State, Null_T)
   is
      Max : Integer := 30;

      type T is private;

      Null_T : constant T;

   private
      Tmp : constant Integer := Max with Part_Of => State;

      type T is new Typ (Tmp);

      Null_T : constant T := (Int => Max);
   end;
end;
