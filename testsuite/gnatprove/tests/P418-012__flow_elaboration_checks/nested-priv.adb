package body Nested.Priv is

   procedure Blah is null;

begin

   Y := Y + 1;
   --  This is OK since Y is not actually publically visible...

end Nested.Priv;
