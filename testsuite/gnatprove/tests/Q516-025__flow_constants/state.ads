package State
is
   Val : constant Integer;

   procedure Proc                with Global => Val;
   function  Func return Integer with Global => Val;

private

   Val : constant Integer := 0;

end State;
