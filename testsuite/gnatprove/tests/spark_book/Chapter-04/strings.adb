pragma SPARK_Mode(On);

package body Strings is

   procedure Search (Text     : in  String;
                     Letter   : in  Character;
                     Start    : in  Positive;
                     Found    : out Boolean;
                     Position : out Positive) is

      Current : Positive;
   begin
      Found := False;
      Position := 1;  -- Somewhat arbitrary.

      -- Make sure the starting position is reasonable.
      if Start in Text'Range then
         Current := Start;
         while Current <= Text'Last loop
            if Text(Current) = Letter then
               Found := True;
               Position := Current;
               return;
            end if;
         end loop;
      end if;
   end Search;

   procedure Get_Value (Text  : in     String;
                        Name  : in     String;
                        Value : in out Integer) is

      Equals_Found    : Boolean;
      Equals_Position : Positive;
   begin
      if Text'Length > 0 then
         Search (Text     => Text,
                 Letter   => '=',
                 Start    => Text'First,
                 Found    => Equals_Found,
                 Position => Equals_Position);

         if Equals_Found then
            if Name = Text (Text'First .. Equals_Position - 1) then
               Value := Integer'Value (Text (Equals_Position + 1 .. Text'Last));
            end if;
         end if;
      end if;
   end Get_Value;

end Strings;
