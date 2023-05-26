procedure Test_Box_In_Aggregate with SPARK_Mode is


    Unused : constant := -16#6789#;
    type Small_Integer is range -16#8000#..16#7FFF#
        with Default_Value => Unused;
    type Sml_Int_Array is array (1 .. 6) of Small_Integer;


   B_Arr : Sml_Int_Array := (1 => 0, 2 => <>, 3 => -4, 4 .. 5 => <>, 6 => <>);

    -- Note: We can't safely write a Ident_Word that directly uses Ident_Int
    -- as the range of Integer might not include Word_16'Last.

 begin
   if B_Arr (2) /= Unused then
      pragma Assert (False);
   end if;

end Test_Box_In_Aggregate;
