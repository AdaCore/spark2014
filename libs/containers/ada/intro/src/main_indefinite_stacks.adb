with Indefinite_Stacks;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main_Indefinite_Stacks is
   type Country is record
      Id : Integer;
      Description : String (1 .. 8);
   end record;
   type Country_Access is access all Country;
   package Countries_Stacks is new Indefinite_Stacks (Country);
   use Countries_Stacks;
   country_default :  aliased Country :=  Country'(1, "12345678");
   country_second :  aliased Country :=  Country'(2, "24681357");
   country_third :  aliased Country :=  Country'(3, "87654321");
   X : Content_Ref;
   --  S : Stack_Ptr := Create (country_default'Unchecked_Access);
   S : Stack_Ptr := Create (null);
begin
   pragma Assert (Is_Empty (S));
   Push (S, country_default'Unchecked_Access);
   pragma Assert (not (Is_Empty (S)));
   X := Pop (S);
   Put_Line (Item => "First pop X.description: " & X.all.Description);
   pragma Assert (X.Id = 1);

   Push (S, country_default'Unchecked_Access);
   Push (S, country_second'Unchecked_Access);
   Push (S, country_third'Unchecked_Access);
   X := Pop (S);
   pragma Assert (X.Id = 3);
   Put_Line (Item => "Second pop X.description: " & X.all.Description);
   Put_Line (Item => "Second pop X.Id: " & Integer'Image (X.all.Id));
   X := Pop (S);
   pragma Assert (X.Id = 2);
   Put_Line (Item => "Third pop X.description: " & X.all.Description);
   Put_Line (Item => "Third pop X.Id: " & Integer'Image (X.all.Id));

   X := Pop (S);
   pragma Assert (X.Id = 1);
   Put_Line (Item => "Fourth pop X.description: " & X.all.Description);
   Put_Line (Item => "Fourth pop X.Id: " & Integer'Image (X.all.Id));
   pragma Assert (Is_Empty (S));

   declare
      type City is record
         Id : Integer;
         Description : String (1 .. 8);
         Zip_Code : Integer;
      end record;
      type City_Access is access all City;
      package  Cities_Stacks is new Indefinite_Stacks (City);
      use Cities_Stacks;
      city_default : aliased City := City'(4, "87654321", 55070);
      Y : Cities_Stacks.Content_Ref;
      T : Cities_Stacks.Stack_Ptr := Create (null);
   begin
      pragma Assert (Is_Empty (T));
      Push (T, city_default'Unchecked_Access);
      pragma Assert (not (Is_Empty (T)));
      Y := Pop (T);
      Put_Line (Item => "Fifth pop Y.description: " & Y.all.Description);
      Put_Line (Item => "Fifth pop Y.Id: " & Integer'Image (Y.all.Id));
      Put_Line (Item => "Fifth pop Y.Zip: " & Integer'Image (Y.all.Zip_Code));
      pragma Assert (Y.Id = 4);
      pragma Assert (Is_Empty (T));
   end;
   Put_Line ("This is the end, Main_Indefinite_Stacks");
end Main_Indefinite_Stacks;
