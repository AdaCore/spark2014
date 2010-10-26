with Common; use Common; use Common.DLL; use Common.OS;
with Test_Astrium_1; use Test_Astrium_1;
with Test_Astrium_2;
with Test_Astrium_3;

procedure Test_Astrium is
   Monitorings : List;
   Recoveries  : Set;
begin
   Monitorings.Append ((Failed => False, Active => False));
   Monitorings.Append ((Failed => False, Active => True));
   Monitorings.Append ((Failed => False, Active => False));

   pragma Assert (Test_Astrium_1.Test_Recovery (Monitorings) = None);

   Recoveries.Insert ((Priority => 1));
   Recoveries.Insert ((Priority => 5));
   Recoveries.Insert ((Priority => 2));

   pragma Assert
     (Test_Astrium_2.Test_Recovery_Highest (Recoveries).Priority = 5);

   Test_Astrium_3.Activate_First_Non_Active (Monitorings);
   Test_Astrium_3.Activate_First_Non_Active (Monitorings);
   Test_Astrium_3.Activate_First_Non_Active (Monitorings);

end Test_Astrium;
