th Indefinite_Stacks;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main_Indefinite_Stacks is

   type Country is record
      Id : Integer;
      Description : String (1 .. 7);
   end record;
   package Countries_Stacks is new Indefinite_Stacks (Country);
   use Countries_Stacks;
   first_country : Country :=  Country'(1, "Eritrea");
   second_country : Country :=  Country'(2, "Namibia");
   third_country : Country :=  Country'(3, "Marocco");
   X : Country;
   S : Stack := Create;
begin
   Put_Line (Item => "begin");
   pragma Assert (Is_Empty (S));
   Push (S, first_country);
   pragma Assert (not (Is_Empty (S)));
   X := Pop (S);
   Put_Line (Item => "First pop X.description: " & X.Description);
   pragma Assert (X.Id = 1);

   Push (S, first_country);
   Push (S, second_country);
   Push (S, third_country);
   X := Pop (S);
   pragma Assert (X.Id = 3);
   Put_Line (Item => "Second pop X.description: " & X.Description);
   Put_Line (Item => "Second pop X.Id: " & Integer'Image (X.Id));
   X := Pop (S);
   pragma Assert (X.Id = 2);
   Put_Line (Item => "Third pop X.description: " & X.Description);
   Put_Line (Item => "Third pop X.Id: " & Integer'Image (X.Id));

   X := Pop (S);
   pragma Assert (X.Id = 1);
   Put_Line (Item => "Fourth pop X.description: " & X.Description);
   Put_Line (Item => "Fourth pop X.Id: " & Integer'Image (X.Id));
   pragma Assert (Is_Empty (S));

   declare
      type City is record
         Id : Integer;
         Description : String (1 .. 6);
         Zip_Code : Integer;
      end record;
      type City_Access is access all City;
      package  Cities_Stacks is new Indefinite_Stacks (City);
      use Cities_Stacks;
      city_default : City := City'(4, "Luanda", 6468);
      Y : City;
      T : Cities_Stacks.Stack := Create;
   begin
      pragma Assert (Is_Empty (T));
      Push (T, city_default);
      pragma Assert (not (Is_Empty (T)));
      Y := Pop (T);
      Put_Line (Item => "Fifth pop Y.description: " & Y.Description);
      Put_Line (Item => "Fifth pop Y.Id: " & Integer'Image (Y.Id));
      Put_Line (Item => "Fifth pop Y.Zip: " & Integer'Image (Y.Zip_Code));
      pragma Assert (Y.Id = 4);
      pragma Assert (Is_Empty (T));
   end;
   Put_Line ("This is the end, Main_Indefinite_Stacks");
end Main_Indefinite_Stacks;

