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

    procedure Set_Something is
    begin
        Entrance_Check;
        State := Config;
    end Set_Something;

    procedure Run is
    begin
        Entrance_Check;
        State := Run;
    end Run;

end Test_Might_Not_Return;
