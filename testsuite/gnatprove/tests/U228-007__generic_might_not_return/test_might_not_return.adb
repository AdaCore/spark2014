package body Test_Might_Not_Return is

    Some_Value_Read_From_Hw : Integer := 1;

    procedure Init is
    begin
        State := Init;
    end Init;

    procedure Die is
    begin
        loop
            -- halt();
            null;
        end loop;
    end Die;

    procedure Entrance_Check is
    begin
        if Some_Value_Read_From_Hw = 1 then
            Die;
        else
            null;
        end if;
    end Entrance_Check;

    procedure Set_Something_Gen is
    begin
        Entrance_Check;
        State := Config;
    end Set_Something_Gen;

    procedure Set_Something is new Set_Something_Gen;

    procedure Run_Gen is
    begin
        Entrance_Check;
        State := Run;
    end Run_Gen;

    procedure Run is new Run_Gen;

end Test_Might_Not_Return;
