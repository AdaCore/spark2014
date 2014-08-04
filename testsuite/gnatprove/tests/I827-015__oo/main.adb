--  Making this unit SPARK requires use of container of indefinite values.
--  See N317-021
pragma SPARK_Mode (Off);

with Instr;       use Instr;
with Instr.Child; use Instr.Child;
with GNAT.IO;     use GNAT.IO;
with Dash_Board;  use Dash_Board;

procedure Main is

   procedure Print_Dash_Board (L : Vector) is
      C : Cursor := First (L);
   begin

      while Has_Element (C) loop
         Element (C).Display_Value;
         Next (C);
      end loop;
      New_Line;

   end Print_Dash_Board;

   DB : Vector;
   Inc, Sec : Integer;

   S  : Speedometer;
   G  : Gauge;
   G1, G2 : Graphic_Gauge;
   C  : Clock;
   CH : Chronometer;
   AC : Accurate_Clock;

begin
   S.Set_Name ("Speed");
   S.Set (45);

   G.Set_Name ("Fuel");
   G.Set (60);

   G1.Set_Name ("Water");
   G1.Set (80);

   G2.Set_Name ("Oil");
   G1.Set (40);

   C.Set_Name ("Time in NY");
   C.Init (12, 15, 0);

   CH.Set_Name ("Chrono");
   CH.Init (0, 0, 0);

   AC.Set_Name ("Time in Paris");
   AC.Init (6, 15, 0);

   DB.Append (S);       -- 1
   DB.Append (G);       -- 2
   DB.Append (G1);      -- 3
   DB.Append (G2);      -- 4
   DB.Append (C);       -- 5
   DB.Append (CH);      -- 6
   DB.Append (AC);      -- 7

   loop
      Print_Dash_board (DB);

      if Graphic_Gauge (DB.Element (3)).Value < 60 then
         Put_Line ("There is a leak in the radiator.");
      end if;
      if Speedometer (DB.Element (1)).Value > 50 then
         Put_Line (" Speed limit is 50 ... ");
      end if;

      if Clock (DB.Element (5)).Seconds
           /= Accurate_Clock (DB.Element (7)).Seconds
      then
         Put_Line (" Your first clock is not very accurate ");
      end if;

      Put ("Give a time increment in milliseconds (0 to terminate) :");
      Get (Inc);
      exit when Inc <= 0;
      Sec := Inc / 1000;

      C := Clock (DB.Element (5));
      Increment (C, Sec);
      DB.Replace_Element (5, C);

      CH := Chronometer (DB.Element (6));
      CH.Increment (Sec);
      DB.Replace_Element (6, CH);

      AC := Accurate_Clock (DB.Element (7));
      AC.Increment (Inc);
      DB.Replace_Element (7, AC);

      G := Gauge (DB.Element (2));
      G.Set (Integer (Float (G.Value)  * (1.0 - Float (Sec) / 3600.0)));
      DB.Replace_Element (2, G);

      G1 := Graphic_Gauge (DB.Element (3));
      G1.Set (Integer (Float (G1.Value)  * (1.0 - Float (Sec) / 3600.0)));
      DB.Replace_Element (3, G1);

      S := Speedometer (DB.Element (1));
      S.Set (S.Value + 2);
   end loop;
-- exception
--   when Others => Put_Line ("I think that's enough for today... Bye");
end Main;
