pragma SPARK_Mode (On);

with Ada.Text_IO;

package body Types is

    procedure Bytes_Put (Buffer : Bytes) with
        SPARK_Mode => Off
    is
        package Modular_Text_IO is new Ada.Text_IO.Modular_IO (Byte);
        S : String (1 .. 6);
    begin
        for I in Natural range Buffer'First .. Buffer'Last loop
            Modular_Text_IO.Put(To => S, Item => Buffer (I), Base => 16);
            if S (4) = '#' then
                Ada.Text_IO.Put ("0" & S (5) & " ");
            else
                Ada.Text_IO.Put (S (4 .. 5) & " ");
            end if;
        end loop;
        Ada.Text_IO.New_Line;
    end Bytes_Put;

    function Convert_To (Buffer : Bytes) return UXX
    is
        Value : UXX := 0;
    begin
        for i in Natural range 0 .. (UXX'Size / 8) - 1 loop
            Value := Value + UXX (Buffer (Buffer'Last - i)) * UXX (256**i);
        end loop;
        return Value;
    end Convert_To;

end Types;
