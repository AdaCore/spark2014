with Stacks;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main is
   package Integer_Stacks is new Stacks (Integer);
                  use Integer_Stacks;
   S                                       : Stack := Create (4, -1);
   X                                       : Integer;

begin

   --  testing stack for Integer values
   --
   pragma Assert (Is_Empty (S));
   Push (S, 1);
   pragma Assert (not (Is_Empty (S)));
   Pop (S, X);
   Put_Line (Item => "First Integer pop            : " & Integer'Image (X));
   pragma Assert (X = 1);
   pragma Assert (Is_Empty (S));

   Push (S, 2);
   Push (S, 3);
   Push (S, 4);
   X := Pop (S);
   Put_Line (Item => "Second Integer pop           : " & Integer'Image (X));
   pragma Assert (X = 4);
   X := Pop (S);
   Put_Line (Item => "Third Integer pop            : " & Integer'Image (X));
   pragma Assert (X = 3);
   X := Pop (S);
   Put_Line (Item => "Fourth Integer pop           : " & Integer'Image (X));
   pragma Assert (X = 2);
   pragma Assert (Is_Empty (S));
   test_Pop_When_Empty (S);

   --  testing stack for Float values
   --
   declare
      package  Float_Stacks is new Stacks (Float);
                  use Float_Stacks;
      T                                    : Float_Stacks.Stack
                                           := Create (4, -2.0);
      U                                    : Float;

   begin
      pragma Assert (Is_Empty (T));
      Push (T, 1.0);
      pragma Assert (not (Is_Empty (T)));
      Pop (T, U);
      Put_Line (Item => "First  Float pop  : " & Float'Image (U));
      pragma Assert (U = 1.0);
      pragma Assert (Is_Empty (T));
      Push (T, 2.0);
      Push (T, 3.0);
      Push (T, 4.0);
      U := Pop (T);
      Put_Line (Item => "Second  Float pop : " & Float'Image (U));
      pragma Assert (U = 4.0);
      U := Pop (T);
      Put_Line (Item => "Third  Float pop  : " & Float'Image (U));
      pragma Assert (U = 3.0);
      U := Pop (T);
      Put_Line (Item => "Fourth  Float pop : " & Float'Image (U));
      pragma Assert (U = 2.0);
      pragma Assert (Is_Empty (T));
      test_Pop_When_Empty (T);
   end;

end Main;
