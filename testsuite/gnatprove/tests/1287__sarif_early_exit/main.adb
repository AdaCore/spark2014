with Ada.Text_IO; use Ada.Text_IO;

procedure Main is
   pragma Extensions_Allowed (All_Extensions);

   procedure Foo is
   begin
      X : Integer;
      X : Float;  -- ERROR: conflicts with declaration
      null;
   end;
begin
   A : constant Integer; -- ERROR: requires initialization

   begin
      B : Integer := 12;
      if (B /= 12) then
         raise Program_Error;
      end if;
   exception
      when others =>
         Put_Line ("B = " & B'Image); -- ERROR: undefined
   end;
end Main;
