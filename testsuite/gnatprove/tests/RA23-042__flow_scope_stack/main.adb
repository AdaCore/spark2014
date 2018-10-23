procedure Main is

   package P is
      type T is private;

   private
      --  When processing Main we descent here to detect objects that will
      --  be lifted into singleton abstract states (e.g. X and Y below) and
      --  to record their initialization data which might be accessed
      --  between the package declaration and the package body.

      type T is record
         C : Integer := 0;
      end record;

      X : T;
      Y : T := X'Update (C => 0);
      --  If we process this 'Update expression with the visibility of T as
      --  a private type, then we will crash when seeing its component.
   end;

begin
   null;
end;
