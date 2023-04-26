package Test_Might_Not_Return is

    type Ghost_State is (Init, Config, Run) with Ghost;
    State : Ghost_State := Init with Ghost;

    procedure Die with No_Return, Exceptional_Cases => (others => False);
    procedure Entrance_Check;

    procedure Init with
        Post => State = Init;

    generic
    procedure Set_Something_Gen with
        Pre => State = Init,
        Post => State = Config;

    generic
    procedure Run_Gen with
        Pre => State = Config,
        Post => State = Run;

end Test_Might_Not_Return;
