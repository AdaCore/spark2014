package DIC2 with SPARK_Mode is

   package Nested is
      type Parent is tagged private
        with Default_Initial_Condition => Is_OK (Parent);

        function Is_OK (Obj : Parent) return Boolean;

   private
      pragma SPARK_Mode (Off);

      type Parent is tagged record
         B : Boolean := True;
      end record;

      function Is_OK (Obj : Parent) return Boolean is (Obj.B);

      P0 : Parent;
      P1 : Parent := (B => True);
   end Nested;
   use Nested;

   type Child is new Parent with private;

   function Is_OK (Obj : Child) return Boolean;

private
   type Child is new Parent with null record;

   function Is_OK (Obj : Child) return Boolean is (not Is_OK (Parent (Obj)));

   C0 : Child;

end DIC2;
