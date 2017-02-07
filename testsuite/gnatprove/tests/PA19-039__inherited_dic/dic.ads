package DIC with SPARK_Mode is

   type Parent is tagged private
     with Default_Initial_Condition => Is_OK (Parent);

   function Is_OK (Obj : Parent) return Boolean;

   type Child is new Parent with private;

   function Is_OK (Obj : Child) return Boolean;

private
   type Parent is tagged record
      B : Boolean := True;
   end record;

   function Is_OK (Obj : Parent) return Boolean is (Obj.B);

   type Child is new Parent with null record;

   function Is_OK (Obj : Child) return Boolean is (not Obj.B);

   P0 : Parent;
   C0 : Child;

   P1 : Parent := (B => True);
   C1 : Child  := (B => False);

end DIC;
