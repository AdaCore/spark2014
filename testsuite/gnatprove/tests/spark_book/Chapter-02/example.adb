with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Example is

   Limit : constant Integer := 1_000;

   procedure Bounded_Increment
     (Value   : in out Integer;  -- A value to increment
      Bound   : in     Integer;  -- The maximum that Value may take
      Changed :    out Boolean)  -- Did Value change?
   is
   begin
      if Value < Bound then
         Value   := Value + 1;
         Changed := True;
      else
         Changed := False;
      end if;
   end Bounded_Increment;

   Value    : Integer;
   Modified : Boolean;

begin -- procedure Example
   Ada.Text_IO.Put_Line ("Enter a number.");
   Ada.Integer_Text_IO.Get (Value);
   Bounded_Increment (Bound   => Limit / 2,
                      Value   => Value,
                      Changed => Modified);
   if Modified then
      Ada.Text_IO.Put_Line ("Your number was changed to ");
      Ada.Integer_Text_IO.Put (Item  => Value,
                                Width => 1);
   end if;
end Example;
